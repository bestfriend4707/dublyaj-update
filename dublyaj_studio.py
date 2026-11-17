#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
DUBLYAJ STUDIO
==============
Original film audiosidan vokal (gap)larni o'chiradi / eshitilmas darajaga tushiradi,
dublyaj ovozi bor joylarda fon (musiqa, shovqin) ni avtomatik pasaytiradi (ducking)
va xohlasangiz dublyaj ovozini ustiga joylab beradi.

  * 2 kanalli (stereo) va 6 kanalli (5.1) audio bilan ishlaydi (7.1 / mono ham qabul qilinadi)
  * Oqimli (streaming) ishlov  ->  2-3 soatlik kino ham kam RAM bilan ishlaydi
  * Ixtiyoriy: tez AI (MDX-Net, pip install onnxruntime) yoki Demucs bilan vokalni ajratish

Talablar:  Python 3.9+,  numpy  (pip install numpy),  FFmpeg + FFprobe
           (ffmpeg.exe va ffprobe.exe ni shu skript yonidagi papkaga yoki PATH ga qo'ying)
"""

import os
import sys
import re
import json
import time
import math
import queue
import shutil
import threading
import subprocess
import tempfile
import collections
import importlib.util
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field, asdict, replace

import numpy as np
from fractions import Fraction

APP_NAME = "Dublyaj Studio"
APP_VERSION = "1.9"
FROZEN = bool(getattr(sys, "frozen", False))      # PyInstaller (.exe) ichida ishlayaptimi

# ----------------------------------------------------------------------------------------
#  LITSENZIYA (aktivatsiya kaliti) va imzolangan yangilanishlar
#  * Kalit — dasturchining maxfiy kaliti bilan imzolangan (Ed25519). Soxta kalit yasab bo'lmaydi.
#  * Kalit shu kompyuterga bog'lanadi (Mashina ID) va aktivlashtirilgan kundan boshlab 1 yil ishlaydi.
#  * Yangilanish kodi ham imzolanadi: imzosiz/begona kod ishga tushmaydi.
# ----------------------------------------------------------------------------------------
LIC_PUB = bytes.fromhex("c3d89f33e26ebd92198bcdb2e18306d7feabb26b54340608b533a533386680a3")
import hashlib as _hl

_P = 2 ** 255 - 19
_Q = 2 ** 252 + 27742317777372353535851937790883648493


def _inv(x):
    return pow(x, _P - 2, _P)


_D = -121665 * _inv(121666) % _P
_I = pow(2, (_P - 1) // 4, _P)


def _rx(y, sign):
    if y >= _P:
        return None
    x2 = (y * y - 1) * _inv(_D * y * y + 1)
    if x2 == 0:
        return None if sign else 0
    x = pow(x2, (_P + 3) // 8, _P)
    if (x * x - x2) % _P:
        x = x * _I % _P
    if (x * x - x2) % _P:
        return None
    if (x & 1) != sign:
        x = _P - x
    return x


_GY = 4 * _inv(5) % _P
_GX = _rx(_GY, 0)
_G = (_GX, _GY, 1, _GX * _GY % _P)


def _add(a, b):
    A = (a[1] - a[0]) * (b[1] - b[0]) % _P
    B = (a[1] + a[0]) * (b[1] + b[0]) % _P
    C = 2 * a[3] * b[3] * _D % _P
    D = 2 * a[2] * b[2] % _P
    E, F, G, H = B - A, D - C, D + C, B + A
    return (E * F % _P, G * H % _P, F * G % _P, E * H % _P)


def _mul(s, pt):
    q = (0, 1, 1, 0)
    while s > 0:
        if s & 1:
            q = _add(q, pt)
        pt = _add(pt, pt)
        s >>= 1
    return q


def _eq(a, b):
    return (a[0] * b[2] - b[0] * a[2]) % _P == 0 and (a[1] * b[2] - b[1] * a[2]) % _P == 0


def _comp(pt):
    z = _inv(pt[2])
    x, y = pt[0] * z % _P, pt[1] * z % _P
    return int.to_bytes(y | ((x & 1) << 255), 32, "little")


def _decomp(s):
    if len(s) != 32:
        return None
    y = int.from_bytes(s, "little")
    sign = y >> 255
    y &= (1 << 255) - 1
    x = _rx(y, sign)
    return None if x is None else (x, y, 1, x * y % _P)


def _h(m):
    return int.from_bytes(_hl.sha512(m).digest(), "little") % _Q


def _expand(seed):
    h = _hl.sha512(seed).digest()
    a = int.from_bytes(h[:32], "little")
    a &= (1 << 254) - 8
    a |= 1 << 254
    return a, h[32:]


def ed_public(seed):
    return _comp(_mul(_expand(seed)[0], _G))


def ed_sign(seed, msg):
    a, prefix = _expand(seed)
    A = _comp(_mul(a, _G))
    r = _h(prefix + msg)
    R = _comp(_mul(r, _G))
    s = (r + _h(R + A + msg) * a) % _Q
    return R + int.to_bytes(s, 32, "little")


def ed_verify(pub, msg, sig):
    try:
        if len(pub) != 32 or len(sig) != 64:
            return False
        A = _decomp(pub)
        R = _decomp(sig[:32])
        if A is None or R is None:
            return False
        s = int.from_bytes(sig[32:], "little")
        if s >= _Q:
            return False
        h = _h(sig[:32] + pub + msg)
        return _eq(_mul(s, _G), _add(R, _mul(h, A)))
    except Exception:
        return False


SIG_TAG = b"\n# DS-SIG:"


def code_sig_ok(data):
    """Kod oxiridagi '# DS-SIG:<hex>' imzosi dasturchi kaliti bilan mosmi?"""
    try:
        i = data.rfind(SIG_TAG)
        if i < 0:
            return False
        sig = bytes.fromhex(data[i + len(SIG_TAG):].strip().decode("ascii"))
        return ed_verify(LIC_PUB, b"UPD1|" + _hl.sha256(data[:i]).digest(), sig)
    except Exception:
        return False


def _machine_raw():
    parts = []
    try:
        if os.name == "nt":
            import winreg
            try:
                k = winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\Microsoft\Cryptography", 0,
                                   winreg.KEY_READ | winreg.KEY_WOW64_64KEY)
                parts.append(str(winreg.QueryValueEx(k, "MachineGuid")[0]))
            except Exception:
                pass
            try:
                import ctypes
                ser = ctypes.c_uint32(0)
                ctypes.windll.kernel32.GetVolumeInformationW(ctypes.c_wchar_p(os.environ.get("SystemDrive", "C:") + "\\"),
                                                             None, 0, ctypes.byref(ser), None, None, None, 0)
                parts.append("%08x" % ser.value)
            except Exception:
                pass
            try:
                k = winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, r"HARDWARE\DESCRIPTION\System\CentralProcessor\0")
                parts.append(str(winreg.QueryValueEx(k, "ProcessorNameString")[0]).strip())
            except Exception:
                pass
        else:
            for f in ("/etc/machine-id", "/var/lib/dbus/machine-id"):
                try:
                    with open(f) as fh:
                        parts.append(fh.read().strip())
                        break
                except OSError:
                    pass
    except Exception:
        pass
    if not parts:
        import uuid
        parts.append("mac%012x" % uuid.getnode())
    return "|".join(parts)


def machine_id():
    return _hl.sha256(b"DS-MID|" + _machine_raw().encode("utf-8", "replace")).digest()[:8]


def machine_id_str():
    h = machine_id().hex().upper()
    return "-".join(h[i:i + 4] for i in range(0, 16, 4))


REVOKE_URL = ""   # make_release.py --revoke-url bilan avtomatik to'ldiriladi (bekor qilingan kalitlar ro'yxati, version.json kabi repoda)
_REVOKE_CACHE_FILE = os.path.join(os.path.expanduser("~"), ".dublyaj_studio", "revoked.json")


def _revoked_ids():
    """Bekor qilingan kalitlar ro'yxati (imzolangan). Internet bo'lsa yangilanadi, bo'lmasa oxirgi ma'lum ro'yxat ishlatiladi."""
    cached = {"ids": [], "t": 0}
    try:
        with open(_REVOKE_CACHE_FILE, encoding="utf-8") as f:
            cached = json.load(f)
    except (OSError, ValueError):
        pass
    if REVOKE_URL and time.time() - cached.get("t", 0) > 3600:
        try:
            raw = upd_fetch(REVOKE_URL, timeout=6)
            d = json.loads(raw.decode("utf-8"))
            sig = bytes.fromhex(d["sig"])
            if ed_verify(LIC_PUB, b"REV1|" + json.dumps(d["ids"], separators=(",", ":")).encode(), sig):
                cached = {"ids": d["ids"], "t": time.time()}
                try:
                    os.makedirs(os.path.dirname(_REVOKE_CACHE_FILE), exist_ok=True)
                    with open(_REVOKE_CACHE_FILE, "w", encoding="utf-8") as f:
                        json.dump(cached, f)
                except OSError:
                    pass
        except Exception:
            pass
    return set(cached.get("ids", []))


LIC_FILES = [os.path.join(os.path.expanduser("~"), ".dublyaj_studio", "lic.dat"),
             os.path.join(os.environ.get("APPDATA") or os.path.join(os.path.expanduser("~"), ".cache"), "dsl.bin")]
LIC_REG = r"Software\Dublyaj\Studio"


def _st_key():
    return _hl.sha256(b"DS-ST|" + _machine_raw().encode("utf-8", "replace") + LIC_PUB).digest()


def _st_pack(d):
    import hmac
    import base64
    body = json.dumps(d, sort_keys=True).encode()
    return base64.b64encode(hmac.new(_st_key(), body, _hl.sha256).digest() + body).decode()


def _st_unpack(s):
    import hmac
    import base64
    try:
        raw = base64.b64decode(s.strip())
        mac, body = raw[:32], raw[32:]
        if not hmac.compare_digest(mac, hmac.new(_st_key(), body, _hl.sha256).digest()):
            return None
        d = json.loads(body.decode())
        return d if isinstance(d, dict) else None
    except Exception:
        return None


def _st_load():
    out = []
    for f in LIC_FILES:
        try:
            with open(f, encoding="ascii") as fh:
                d = _st_unpack(fh.read())
                if d:
                    out.append(d)
        except OSError:
            pass
    if os.name == "nt":
        try:
            import winreg
            k = winreg.OpenKey(winreg.HKEY_CURRENT_USER, LIC_REG)
            d = _st_unpack(str(winreg.QueryValueEx(k, "State")[0]))
            if d:
                out.append(d)
        except Exception:
            pass
    return out


def _st_save(d):
    s = _st_pack(d)
    for f in LIC_FILES:
        try:
            os.makedirs(os.path.dirname(f), exist_ok=True)
            with open(f, "w", encoding="ascii") as fh:
                fh.write(s)
        except OSError:
            pass
    if os.name == "nt":
        try:
            import winreg
            k = winreg.CreateKey(winreg.HKEY_CURRENT_USER, LIC_REG)
            winreg.SetValueEx(k, "State", 0, winreg.REG_SZ, s)
        except Exception:
            pass


def lic_parse(keystr):
    """Kalit matnini tekshiradi. Imzo noto'g'ri bo'lsa ValueError. Qaytaradi: dict."""
    import base64
    import struct
    t = (keystr or "").strip().upper()
    if t.startswith("DSK-"):
        t = t[4:]
    t = re.sub(r"[^A-Z2-7]", "", t)
    try:
        raw = base64.b32decode(t + "=" * (-len(t) % 8))
    except Exception:
        raise ValueError("Kalit formati noto'g'ri.")
    if len(raw) < 64 + 25:
        raise ValueError("Kalit to'liq emas (nusxalashda uzilgan bo'lishi mumkin).")
    payload, sig = raw[:-64], raw[-64:]
    if not ed_verify(LIC_PUB, b"LIC1|" + payload, sig):
        raise ValueError("Kalit noto'g'ri (imzo mos kelmadi).")
    try:
        ver, kid, issued, act_by, days, flags, mach, nl = struct.unpack(">B4sIIHB8sB", payload[:25])
        name = payload[25:25 + nl].decode("utf-8", "replace")
    except Exception:
        raise ValueError("Kalit buzilgan.")
    if ver != 1:
        raise ValueError("Kalit versiyasi qo'llab-quvvatlanmaydi.")
    return dict(kid=kid.hex(), issued=issued, act_by=act_by, days=days, any=bool(flags & 1), machine=mach,
                name=name, key="DSK-" + "-".join(t[i:i + 6] for i in range(0, len(t), 6)))


def _lic_for_machine(info):
    return info["any"] or info["machine"] == machine_id()


def _net_time():
    """Internet bo'lsa haqiqiy vaqt (soat o'zgartirilganini aniqlash uchun). Yo'q bo'lsa None."""
    try:
        import urllib.request
        from email.utils import parsedate_to_datetime
        r = urllib.request.urlopen(urllib.request.Request("https://api.github.com", method="HEAD",
                                   headers={"User-Agent": "DublyajStudio"}), timeout=4)
        return parsedate_to_datetime(r.headers["Date"]).timestamp()
    except Exception:
        try:
            import urllib.request
            from email.utils import parsedate_to_datetime
            r = urllib.request.urlopen(urllib.request.Request("https://www.google.com", method="HEAD"), timeout=4)
            return parsedate_to_datetime(r.headers["Date"]).timestamp()
        except Exception:
            return None


_LIC_CACHE = {"t": 0.0, "v": None}


def lic_status(force=False):
    """(ok, info, xabar). info: name, expiry, days_left."""
    now = time.time()
    if not force and _LIC_CACHE["v"] is not None and now - _LIC_CACHE["t"] < 20:
        return _LIC_CACHE["v"]
    res = _lic_status(now)
    _LIC_CACHE["t"], _LIC_CACHE["v"] = now, res
    return res


def _lic_status(now):
    best, seen = None, 0.0
    for st in _st_load():
        try:
            info = lic_parse(st["key"])
            if not _lic_for_machine(info):
                continue
            act = float(st["act"])
            seen = max(seen, float(st.get("seen", act)))
            if best is None or (info["issued"], -act) > (best[0]["issued"], -best[1]):
                best = (info, act)
        except Exception:
            continue
    if best is None:
        return False, None, "Dastur aktivlashtirilmagan."
    info, act = best
    if info["kid"] in _revoked_ids():
        return False, None, "Bu kalit bekor qilingan. Yangi kalit uchun dasturchiga murojaat qiling."
    if now < seen - 86400:
        return False, None, "Kompyuter soati orqaga o'zgartirilgan. Soatni to'g'rilang."
    expiry = act + info["days"] * 86400
    if now > expiry:
        return False, None, "Litsenziya muddati tugagan. Yangi kalit oling."
    if now > seen + 600:
        _st_save({"key": info["key"], "act": act, "seen": now})
    return True, dict(name=info["name"], expiry=expiry, days_left=int((expiry - now) // 86400) + 1), ""


def lic_activate(keystr):
    """Kalitni tekshirib aktivlashtiradi. Xato bo'lsa ValueError."""
    info = lic_parse(keystr)
    if not _lic_for_machine(info):
        raise ValueError("Bu kalit boshqa kompyuter uchun berilgan (Mashina ID mos emas).")
    now = time.time()
    act = None
    for st in _st_load():
        try:
            if lic_parse(st["key"])["kid"] == info["kid"]:
                act = float(st["act"]) if act is None else min(act, float(st["act"]))
        except Exception:
            pass
    if act is None:
        if int(now // 86400) > info["act_by"]:
            raise ValueError("Bu kalitni aktivlashtirish muddati o'tgan. Yangi kalit oling.")
        nt = _net_time()
        if nt and abs(nt - now) > 2 * 86400:
            raise ValueError("Kompyuter soati noto'g'ri. Sana va vaqtni to'g'rilab qayta urinib ko'ring.")
        act = now
    if now > act + info["days"] * 86400:
        raise ValueError("Litsenziya muddati tugagan. Yangi kalit oling.")
    _st_save({"key": info["key"], "act": act, "seen": now})
    _LIC_CACHE["v"] = None
    return lic_status(True)


def lic_require():
    ok, _info, msg = lic_status()
    if not ok:
        raise RuntimeError("Litsenziya: " + msg)



# ----------------------------------------------------------------------------------------
#  YANGILASH (UPDATE): EXE ni qayta build qilmasdan dasturni yangilash
#  Yangi dublyaj_studio.py  ~/.dublyaj_studio/update/  papkasiga qo'yiladi. Keyingi ishga tushirishda uning
#  versiyasi (APP_VERSION) yuqori bo'lsa, shu fayl ishlaydi (EXE ichidagi Python va kutubxonalar bilan).
#  Xato bo'lsa — avtomatik EXE ichidagi asl nusxaga qaytadi.
# ----------------------------------------------------------------------------------------
UPD_DIR = os.path.join(os.path.expanduser("~"), ".dublyaj_studio", "update")
UPD_FILE = os.path.join(UPD_DIR, "dublyaj_studio.py")


def vtuple(v):
    return tuple(int(x) for x in re.findall(r"\d+", str(v))[:4]) or (0,)


def src_version(text):
    m = re.search(r'^APP_VERSION\s*=\s*"([^"]+)"', text, re.M)
    return m.group(1) if m else None


def _run_override():
    """Yangilangan nusxa bor va yangiroq bo'lsa — uni ishlatadi. True = u ishlab bo'ldi."""
    if globals().get("_IS_OVERRIDE") or os.environ.get("DUBLYAJ_NO_UPDATE") or __name__ != "__main__":
        return False
    try:
        if not os.path.isfile(UPD_FILE):
            return False
        with open(UPD_FILE, "rb") as f:
            raw = f.read()
        if not code_sig_ok(raw):                    # imzosiz / begona kod ishga tushirilmaydi
            raise ValueError("imzo")
        txt = raw.decode("utf-8")
        v = src_version(txt)
        if not v or vtuple(v) <= vtuple(APP_VERSION):
            return False
        code = compile(txt, UPD_FILE, "exec")
    except Exception:
        try:
            os.replace(UPD_FILE, UPD_FILE + ".bad")
        except OSError:
            pass
        return False
    g = {"__name__": "__main__", "__file__": UPD_FILE, "_IS_OVERRIDE": True, "__builtins__": __builtins__}
    try:
        exec(code, g)
        return True
    except SystemExit:
        raise
    except BaseException:                           # yangilanish buzuq — asl nusxaga qaytamiz
        import traceback
        try:
            with open(os.path.join(UPD_DIR, "update_error.txt"), "w", encoding="utf-8") as f:
                f.write(traceback.format_exc())
            os.replace(UPD_FILE, UPD_FILE + ".bad")
        except OSError:
            pass
        return False


if __name__ == "__main__" and _run_override():
    sys.exit(0)

SR = 48000                      # ishlov chastotasi (kino standarti)
NFFT = 4096                     # STFT oynasi
HOP = NFFT // 4
SEG_SEC = 20                    # bir bo'lak uzunligi (soniya)
CTX = 16384                     # bo'laklar chegarasidagi kontekst (namuna)
ENV_HOP = 0.010                 # ducking egri chizig'i qadami: 10 ms
ENV_SR = 16000                  # dublyaj tahlili uchun chastota

FORMATS = {
    "WAV 24-bit (PCM)":                    dict(ext=".wav",  kind="wav"),
    "FLAC (lossless)":                     dict(ext=".flac", kind="flac"),
    "AC3 — Dolby Digital":                 dict(ext=".ac3",  kind="ac3"),
    "E-AC3 — Dolby Digital Plus":          dict(ext=".eac3", kind="eac3"),
    "AAC (.m4a)":                          dict(ext=".m4a",  kind="aac"),
    "MP3 (faqat stereo)":                  dict(ext=".mp3",  kind="mp3"),
    "MKV — video + yangi audio (AC3)":     dict(ext=".mkv",  kind="ac3", video=True),
    "MP4 — video + yangi audio (AAC)":     dict(ext=".mp4",  kind="aac", video=True),
}

FC_LABELS = {
    "soft": "Yumshoq pasaytirish — fon/effekt qoladi (dublyaj rejimida tavsiya)",
    "mute": "To'liq o'chirish (tez, effektlar ham ketadi)",
    "transient": "O'chirish, lekin o'q/portlashni saqlash",
    "ai": "AI (MDX-Net/Demucs) — eng sifatli, faqat AI rejimida",
    "keep": "Tegmaslik",
}

ENGINE_LABELS = {"fast": "Tez AI (MDX-Net) — tavsiya", "hq": "Sifatli AI (MDX Voc_FT)", "demucs": "Demucs (juda sekin)"}
OUTCH_LABELS = {"auto": "Kanallar: original kabi", "2": "Kanallar: Stereo (2.0)", "6": "Kanallar: 5.1"}

PRESETS = {
    "Professional (original ovozsiz, fon saqlanadi)": dict(
        vocal_cut=45, f_lo=100, f_hi=10000, sharp=1.2, center_cut=70, protect=90, dip_db=10, leak_cancel=100,
        fc_soft_db=30, mask_margin=32, mask_max_red=40, mask_release=350, bed_keep=85, bed_margin=14,
        pad_ms=1300, pad_dip=26, duck_db=1, thr_db=-50, attack=25, release=300, hold=450, look=80,
        bg_db=0, dub_db=0, dub_target=-17, dub_level_up=6, fc="soft", surr=True, side=True, side_margin=10, side_max_red=14, mode="dsp"),
    "Standart (tavsiya)":            dict(vocal_cut=30, f_lo=120, f_hi=9000, sharp=2.0, center_cut=60, protect=0, dip_db=0,
                                          fc_soft_db=12, mask_margin=20, mask_max_red=24, mask_release=300, bed_keep=85, bed_margin=12, pad_ms=1000, pad_dip=20,
                                          duck_db=4, thr_db=-50, attack=30, release=250, hold=400, look=60, fc="soft", dub_target=-18, dub_level_up=0, leak_cancel=100, bg_db=0, dub_db=0, side=False, mode="dsp"),
    "Kuchli vokal o'chirish":        dict(vocal_cut=50, f_lo=70, f_hi=11000, sharp=0.75, center_cut=80, protect=0, dip_db=6,
                                          fc_soft_db=20, mask_margin=26, mask_max_red=30, mask_release=350, bed_keep=60, bed_margin=16, pad_ms=1500, pad_dip=28,
                                          duck_db=6, thr_db=-50, attack=25, release=300, hold=400, look=80, fc="soft", dub_target=-18, dub_level_up=0, leak_cancel=100, bg_db=0, dub_db=0, side=False, mode="dsp"),
    "O'q/portlash saqlansin":        dict(vocal_cut=30, f_lo=120, f_hi=9000, sharp=2.0, center_cut=60, protect=80, dip_db=0,
                                          fc_soft_db=12, mask_margin=20, mask_max_red=24, mask_release=300, bed_keep=85, bed_margin=12, pad_ms=1000, pad_dip=20,
                                          duck_db=4, thr_db=-50, attack=30, release=250, hold=400, look=60, fc="transient", dub_target=-18, dub_level_up=0, leak_cancel=100, bg_db=0, dub_db=0, side=False, mode="dsp"),
    "Yumshoq (fon ko'proq eshitilsin)": dict(vocal_cut=24, f_lo=180, f_hi=7000, sharp=3.0, center_cut=60, protect=0, dip_db=0,
                                          fc_soft_db=8, mask_margin=15, mask_max_red=18, mask_release=250, bed_keep=100, bed_margin=8, pad_ms=700, pad_dip=14,
                                          duck_db=3, thr_db=-48, attack=40, release=300, hold=450, look=60, fc="soft", dub_target=-18, dub_level_up=0, leak_cancel=100, bg_db=0, dub_db=0, side=False, mode="dsp"),
}

PRESETS["Professional AI (tez: nutq eng toza, effektlar saqlanadi)"] = dict(
    PRESETS["Professional (original ovozsiz, fon saqlanadi)"], mode="ai", fc="ai", dip_db=0, protect=70,
    mask_margin=26, mask_max_red=32)
PRESETS["Frame (studiya darajasi: faqat inson gaplari o'chadi, fon saqlanadi)"] = dict(
    PRESETS["Professional AI (tez: nutq eng toza, effektlar saqlanadi)"],
    vocal_cut=45, center_cut=70, protect=85, dip_db=0, duck_db=0.5, bg_db=0,
    mask_margin=28, mask_max_red=34, mask_release=300, bed_keep=92, bed_margin=14,
    pad_ms=1000, pad_dip=28, thr_db=-50, hold=400, look=100, attack=20, release=250,
    dub_target=-18, dub_level_up=4, dub_db=0, mode="ai", fc="ai", ai_all=True)
# "Frame": AI faqat nutqni oladi (effekt/shovqin qoladi), dublyaj balandligi o'rtacha (-18 dBFS), past joylari +4 dB gacha tekislanadi.
# AI rejimida ovoz Demucs bilan ajratiladi: effektlar (eshik, qadam) FC da ham qoladi, shuning uchun
# qo'shimcha DSP pasaytirishlar yumshatilgan.

PRESETS["Frame+ (faqat inson gaplari o'chadi, fon 100% o'zgarmaydi, Sifatli AI)"] = dict(
    PRESETS["Frame (studiya darajasi: faqat inson gaplari o'chadi, fon saqlanadi)"],
    # Dublyaj bor joyda fon/shovqin/effektlar HECH QANAQA pasaytirilmaydi — faqat AI ajratgan
    # inson ovozi olib tashlanadi, qolgani original holicha qoladi:
    duck_db=0, bg_db=0, dip_db=0,
    protect=95,                       # portlash/eshik kabi o'tkinchi effektlarni yanada ko'proq himoyalaydi
    ai_engine="hq",                   # "Sifatli AI (MDX Voc_FT)" — nutqni eng to'liq ajratadigan dvigatel
    ai_all=True, guided=True, mask_on=True,
    # Qoldiq ovoz (AI to'liq olib tashlay olmagan juda oz miqdordagi "sizib chiqish")ni tozalaydi,
    # lekin haqiqiy fon/effektlarga tegmaydi (bed_keep=100 — fon butunlay saqlanadi):
    mask_margin=30, mask_max_red=30, mask_release=300, bed_keep=100, bed_margin=14,
    pad_ms=1000, pad_dip=28,
    # Dublyaj past bo'lsa, ko'rish paytida eshitilmay qolmasligi uchun biroz ko'tariladi (balans saqlanadi):
    dub_target=-17, dub_level_up=6, dub_db=0, auto_dub=True,
    mode="ai", fc="ai")
# "Frame+": duck_db/bg_db/dip_db = 0 — dublyaj bor joyda original fon/shovqin ASLO pasaytirilmaydi;
# faqat AI (Sifatli dvigatel) ajratgan inson ovozi to'liq olib tashlanadi. bed_keep=100 bilan
# niqoblash bosqichi ham haqiqiy fonga tegmaydi, faqat AI qoldirgan nozik vokal izlarini tozalaydi.
# GPU/CPU tanlovi presetga bog'liq emas — bu avtomatik ravishda o'rnatilgan onnxruntime turi va
# videokarta mavjudligiga qarab aniqlanadi (boshqa AI presetlar bilan bir xil tarzda).


# ----------------------------------------------------------------------------------------
#  Yordamchi funksiyalar
# ----------------------------------------------------------------------------------------
class Cancelled(Exception):
    pass


def _flags():
    return subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0


def app_dir():
    """Dastur papkasi (.exe bo'lsa — .exe yonidagi papka; ffmpeg, models shu yerdan qidiriladi)."""
    if FROZEN:
        return os.path.dirname(os.path.abspath(sys.executable))
    try:
        return os.path.dirname(os.path.abspath(__file__))
    except NameError:
        return os.getcwd()


def find_tool(name):
    exe = name + (".exe" if os.name == "nt" else "")
    base = app_dir()
    cands = [base, os.path.join(base, "ffmpeg"), os.path.join(base, "bin"), os.path.join(base, "ffmpeg", "bin")]
    if getattr(sys, "_MEIPASS", None):
        cands += [sys._MEIPASS, os.path.join(sys._MEIPASS, "bin")]
    for d in cands:
        p = os.path.join(d, exe)
        if os.path.isfile(p):
            return p
    return shutil.which(name)


def fmt_time(sec):
    sec = max(0, int(sec))
    h, r = divmod(sec, 3600)
    m, s = divmod(r, 60)
    return f"{h:d}:{m:02d}:{s:02d}" if h else f"{m:02d}:{s:02d}"


def probe(ffprobe, path):
    """Fayl haqida ma'lumot: audio oqimlar, video bor-yo'qligi, davomiylik."""
    r = subprocess.run(
        [ffprobe, "-v", "error", "-print_format", "json", "-show_streams", "-show_format", path],
        capture_output=True, creationflags=_flags())
    if r.returncode != 0:
        raise RuntimeError("ffprobe faylni o'qiy olmadi:\n" + r.stderr.decode("utf-8", "replace")[-500:])
    j = json.loads(r.stdout.decode("utf-8", "replace") or "{}")
    fdur = 0.0
    try:
        fdur = float(j.get("format", {}).get("duration") or 0)
    except ValueError:
        pass
    audio, has_video, rel = [], False, 0
    for s in j.get("streams", []):
        if s.get("codec_type") == "video" and not s.get("disposition", {}).get("attached_pic"):
            has_video = True
        if s.get("codec_type") == "audio":
            try:
                d = float(s.get("duration") or 0) or fdur
            except ValueError:
                d = fdur
            tags = s.get("tags", {}) or {}
            audio.append(dict(rel=rel, index=s.get("index"), codec=s.get("codec_name", "?"),
                              channels=int(s.get("channels") or 2),
                              layout=s.get("channel_layout", ""), rate=s.get("sample_rate", ""),
                              lang=tags.get("language", ""), title=tags.get("title", ""), duration=d))
            rel += 1
    return dict(audio=audio, has_video=has_video, duration=fdur)


def describe_stream(a):
    extra = " ".join(x for x in (f"[{a['lang']}]" if a["lang"] else "", a["title"]) if x)
    return f"#{a['rel']}  {a['codec'].upper()}  {a['channels']} kanal ({a['layout'] or '?'})  {a['rate']} Hz  {extra}".strip()


class FF:
    """ffmpeg jarayoni (stderr alohida oqimda o'qib turiladi - qotib qolmaslik uchun)."""

    def __init__(self, cmd, stdin=False, stdout=False):
        self.cmd = cmd
        self.p = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE if stdin else subprocess.DEVNULL,
            stdout=subprocess.PIPE if stdout else subprocess.DEVNULL,
            stderr=subprocess.PIPE, bufsize=1 << 22, creationflags=_flags())
        self.err = collections.deque(maxlen=30)
        threading.Thread(target=self._drain, daemon=True).start()

    def _drain(self):
        try:
            for line in iter(self.p.stderr.readline, b""):
                self.err.append(line.decode("utf-8", "replace").rstrip())
        except Exception:
            pass

    def tail(self):
        return "\n".join(self.err)

    def kill(self):
        try:
            self.p.kill()
        except Exception:
            pass

    def finish(self, timeout=None):
        try:
            if self.p.stdin:
                self.p.stdin.close()
        except Exception:
            pass
        self.p.wait(timeout)
        return self.p.returncode


def read_n(ff, ch, n):
    """n ta namuna (n, ch) float32 o'qiydi. Fayl tugasa kamroq qaytaradi."""
    bpf = 4 * ch
    data = ff.p.stdout.read(n * bpf)
    got = len(data) // bpf
    if got == 0:
        return np.zeros((0, ch), np.float32)
    return np.frombuffer(data, dtype="<f4", count=got * ch).reshape(got, ch)


def read_pad(ff, ch, n):
    a = read_n(ff, ch, n)
    if len(a) < n:
        a = np.concatenate([a, np.zeros((n - len(a), ch), np.float32)])
    return a


# ----------------------------------------------------------------------------------------
#  Tez AI: MDX-Net (ONNX Runtime) — Demucs'dan 3-10 marta tezroq
# ----------------------------------------------------------------------------------------
MDX_URL = "https://github.com/TRvlvr/model_repo/releases/download/all_public_uvr_models/"
MDX_MODELS = {
    "fast": dict(file="UVR_MDXNET_9482.onnx", n_fft=6144, dim_f=2048, dim_t=256, comp=1.035, mb=30,
                 label="Tez (MDX-Net, ~30 MB)"),
    "hq": dict(file="UVR-MDX-NET-Voc_FT.onnx", n_fft=7680, dim_f=3072, dim_t=256, comp=1.021, mb=67,
               label="Sifatli (MDX-Net Voc_FT, ~67 MB, sekinroq)"),
}
MDX_HOP = 1024
MDX_SR = 44100


def _avail_ram_mb():
    """Bo'sh operativ xotira (MB); bilib bo'lmasa None."""
    try:
        if os.name == "nt":
            import ctypes

            class MS(ctypes.Structure):
                _fields_ = [("l", ctypes.c_ulong), ("load", ctypes.c_ulong), ("tot", ctypes.c_ulonglong),
                            ("av", ctypes.c_ulonglong), ("a", ctypes.c_ulonglong), ("b", ctypes.c_ulonglong),
                            ("c", ctypes.c_ulonglong), ("d", ctypes.c_ulonglong), ("e", ctypes.c_ulonglong)]
            m = MS()
            m.l = ctypes.sizeof(MS)
            ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(m))
            return m.av / 1048576
        with open("/proc/meminfo") as f:
            for ln in f:
                if ln.startswith("MemAvailable"):
                    return int(ln.split()[1]) / 1024
    except Exception:
        pass
    return None


def mdx_dir():
    d = os.path.join(os.path.expanduser("~"), ".dublyaj_studio", "models")
    os.makedirs(d, exist_ok=True)
    return d


def mdx_find(key):
    """Model faylini qidiradi: avval dastur yonidagi models/ (EXE bilan birga), keyin foydalanuvchi papkasi."""
    fn = MDX_MODELS[key]["file"]
    for d in (os.path.join(app_dir(), "models"), mdx_dir()):
        p = os.path.join(d, fn)
        if os.path.isfile(p) and os.path.getsize(p) > 10_000_000:
            return p
    return None


def mdx_have(key):
    return mdx_find(key) is not None


def mdx_download(key, log=None, cancel=None):
    """Modelni bir marta yuklab oladi (~/.dublyaj_studio/models)."""
    import urllib.request
    m = MDX_MODELS[key]
    dst = os.path.join(mdx_dir(), m["file"])
    found = mdx_find(key)
    if found:
        return found
    if log:
        log(f"AI modeli yuklab olinmoqda ({m['file']}, ~{m['mb']} MB) — faqat birinchi marta...")
    tmp = dst + ".part"
    with urllib.request.urlopen(MDX_URL + m["file"], timeout=60) as r, open(tmp, "wb") as f:
        while True:
            if cancel:
                cancel()
            b = r.read(1 << 20)
            if not b:
                break
            f.write(b)
    os.replace(tmp, dst)
    return dst


def _prepare_ort_dlls():
    """EXE (Windows): onnxruntime DLL lari aynan dastur ichidagisi yuklansin (System32 dagi eskisi emas)."""
    if os.name != "nt" or not FROZEN:
        return
    import ctypes
    base = getattr(sys, "_MEIPASS", app_dir())
    cap = os.path.join(base, "onnxruntime", "capi")
    for d in (cap, base, app_dir()):
        if os.path.isdir(d):
            try:
                os.add_dll_directory(d)
            except Exception:
                pass
    for d, names in ((base, ("vcruntime140.dll", "vcruntime140_1.dll", "msvcp140.dll", "msvcp140_1.dll")),
                     (cap, ("DirectML.dll", "onnxruntime.dll"))):
        for fn in names:
            p = os.path.join(d, fn)
            if os.path.isfile(p):
                try:
                    ctypes.WinDLL(p)
                except Exception:
                    pass


class MDX:
    """UVR MDX-Net ONNX modeli: stereo (N,2) 44.1 kHz -> vokal bahosi."""

    def __init__(self, key, log=None):
        _prepare_ort_dlls()
        import onnxruntime as ort
        self.m = m = MDX_MODELS[key]
        self.n_fft, self.dim_f, self.dim_t, self.comp = m["n_fft"], m["dim_f"], m["dim_t"], m["comp"]
        self.chunk = MDX_HOP * (self.dim_t - 1)
        self.win = (0.5 - 0.5 * np.cos(2 * np.pi * np.arange(self.n_fft) / self.n_fft)).astype(np.float32)
        path = mdx_download(key, log)
        avail = ort.get_available_providers()
        prefs = [p for p in ("CUDAExecutionProvider", "DmlExecutionProvider") if p in avail] + ["CPUExecutionProvider"]
        ncpu = max(1, os.cpu_count() or 2)
        self.sess = None
        for prov in prefs:
            try:
                # CPU: har yadroga bitta 1-oqimli sessiya (intra-op dan ~1.5x tezroq); GPU: bitta sessiya
                n = min(ncpu, 6) if prov == "CPUExecutionProvider" else 1
                ram = _avail_ram_mb()
                if ram is not None:                                  # har sessiya ~0.6-1 GB xotira oladi
                    n = max(1, min(n, int((ram - 1500) // (1000 if key == "hq" else 700))))
                so = ort.SessionOptions()
                so.intra_op_num_threads = 1 if prov == "CPUExecutionProvider" else ncpu
                so.inter_op_num_threads = 1
                if prov == "DmlExecutionProvider":                   # DirectML talabi
                    so.enable_mem_pattern = False
                    so.execution_mode = ort.ExecutionMode.ORT_SEQUENTIAL
                ss = [ort.InferenceSession(path, so, providers=[prov]) for _ in range(n)]
                self.name = ss[0].get_inputs()[0].name
                ss[0].run(None, {self.name: np.zeros((1, 4, self.dim_f, self.dim_t), np.float32)})   # sinov
                self.sess, self.prov, self.sessions = ss[0], prov, ss
                break
            except Exception as e:                         # noqa
                if log:
                    log(f"{prov} ishlamadi ({str(e)[:80]}), keyingisi sinaladi.")
        if self.sess is None:
            raise RuntimeError("ONNX Runtime modelni ishga tushira olmadi.")
        self.n = len(self.sessions)
        self.pool = ThreadPoolExecutor(self.n) if self.n > 1 else None
        self.idx = np.arange(self.dim_t)[:, None] * MDX_HOP + np.arange(self.n_fft)[None, :]
        if self.prov == "CPUExecutionProvider" and self.n >= 4:
            self._tune(key, log)
        self.idx = np.arange(self.dim_t)[:, None] * MDX_HOP + np.arange(self.n_fft)[None, :]
        env = np.zeros(self.chunk + self.n_fft, np.float32)
        for t in range(self.dim_t):
            env[t * MDX_HOP:t * MDX_HOP + self.n_fft] += self.win ** 2
        self.env = np.maximum(env, 1e-8)

    def _tune(self, key, log=None):
        """Ko'p yadroli CPU'da eng tez parallel sessiyalar sonini topadi (giper-oqimlar xotirani to'sib qo'yishi mumkin).
        Natija bir marta o'lchanib eslab qolinadi."""
        f = os.path.join(os.path.expanduser("~"), ".dublyaj_studio", "tune.json")
        tag = "%s-%s-%d" % (key, os.cpu_count(), self.n)
        try:
            with open(f, encoding="utf-8") as fh:
                saved = json.load(fh)
        except (OSError, ValueError):
            saved = {}
        k = saved.get(tag)
        if not isinstance(k, int) or not 1 <= k <= self.n:
            x = (np.random.RandomState(2).randn(self.chunk, 2) * 0.05).astype(np.float32)
            cands = sorted({self.n, max(2, (self.n * 3) // 4), max(2, self.n // 2)}, reverse=True)
            best, k = None, self.n
            if log:
                log("AI tezligi sozlanmoqda (bir martalik, ~20 soniya)...")
            for c in cands:
                try:
                    pool = ThreadPoolExecutor(c)
                    list(pool.map(lambda i: self.vocals(x, i), range(c)))             # isitish
                    t0 = time.time()
                    list(pool.map(lambda i: self.vocals(x, i), range(c)))
                    per = (time.time() - t0) / c
                    pool.shutdown()
                except Exception:                                                     # noqa
                    break
                if best is None or per < best * 0.95:                                 # sezilarli yaxshi bo'lsa almashtiriladi
                    best, k = per, c
            saved[tag] = k
            try:
                os.makedirs(os.path.dirname(f), exist_ok=True)
                with open(f, "w", encoding="utf-8") as fh:
                    json.dump(saved, fh)
            except OSError:
                pass
        if k < self.n:
            self.sessions = self.sessions[:k]
            self.n = k
            self.pool = ThreadPoolExecutor(k) if k > 1 else None
        if log:
            log(f"AI parallel oqimlar: {self.n}")

    def vocals_many(self, xs):
        """Bir nechta bo'lakni parallel ishlaydi (har bir sessiyaga bittadan)."""
        if self.pool is None or len(xs) == 1:
            return [self.vocals(x) for x in xs]
        return list(self.pool.map(lambda a: self.vocals(a[1], a[0] % self.n), enumerate(xs)))

    def vocals(self, x, k=0):
        """x: (chunk, 2) float32 -> (chunk, 2) vokal bahosi."""
        nf, T = self.n_fft, self.dim_t
        xp = np.pad(x.T, ((0, 0), (nf // 2, nf // 2)), mode="reflect")
        fr = xp[:, self.idx] * self.win                                   # (2, T, nf)
        S = np.fft.rfft(fr, axis=-1)[:, :, :self.dim_f].transpose(0, 2, 1)   # (2, F, T)
        inp = np.stack([S.real, S.imag], axis=1).reshape(1, 4, self.dim_f, T).astype(np.float32)
        y = self.sessions[k].run(None, {self.name: inp})[0].reshape(2, 2, self.dim_f, T)
        Y = np.zeros((2, nf // 2 + 1, T), np.complex64)
        Y[:, :self.dim_f, :] = y[:, 0] + 1j * y[:, 1]
        fr2 = np.fft.irfft(Y.transpose(0, 2, 1), n=nf, axis=-1).astype(np.float32) * self.win
        o = np.zeros((2, self.chunk + nf), np.float32)
        for t in range(T):
            o[:, t * MDX_HOP:t * MDX_HOP + nf] += fr2[:, t]
        o = o / self.env
        return (o[:, nf // 2:nf // 2 + self.chunk] * self.comp).T


# ----------------------------------------------------------------------------------------
#  DSP: markazdagi (vokal) komponentani spektral maska bilan pasaytirish
# ----------------------------------------------------------------------------------------
WIN = (0.5 - 0.5 * np.cos(2 * np.pi * np.arange(NFFT) / NFFT)).astype(np.float32)
FREQS = np.arange(NFFT // 2 + 1) * SR / NFFT


_POOL = ThreadPoolExecutor(max_workers=max(1, min(4, (os.cpu_count() or 2))))


def pmap(fn, items):
    """Kanallarni parallel ishlash (numpy FFT/cumsum GIL ni qo'yib yuboradi)."""
    items = list(items)
    if len(items) < 2:
        return [fn(x) for x in items]
    return list(_POOL.map(fn, items))


try:                                    # scipy bo'lsa FFT float32 da tezroq ishlaydi (ixtiyoriy)
    from scipy import fft as FFT
except Exception:
    FFT = np.fft


def _stft(x):
    m = len(x)
    total = m + 2 * NFFT
    rem = (total - NFFT) % HOP
    if rem:
        total += HOP - rem
    xp = np.zeros(total, np.float32)
    xp[NFFT:NFFT + m] = x
    fr = np.lib.stride_tricks.sliding_window_view(xp, NFFT)[::HOP]
    return FFT.rfft(fr * WIN, axis=1)


def _istft(X, m):
    fr = FFT.irfft(X, n=NFFT, axis=1) * WIN
    f = fr.shape[0]
    out = np.zeros((f + 3, HOP), np.float64)
    for k in range(4):                       # hop = NFFT/4
        out[k:k + f] += fr[:, k * HOP:(k + 1) * HOP]
    y = out.reshape(-1) / 1.5               # sum(hann^2) = 1.5
    return y[NFFT:NFFT + m].astype(np.float32)


def _movavg(a, k, axis):
    if k <= 1:
        return a
    if k <= 9:                               # kichik oyna: siljitilgan yig'indi (tez, float32)
        pl = k // 2
        pw = [(0, 0)] * a.ndim
        pw[axis] = (pl, k - 1 - pl)
        ap = np.pad(a.astype(np.float32, copy=False), pw, mode="edge")
        n = a.shape[axis]
        acc = None
        for i in range(k):
            sl = [slice(None)] * a.ndim
            sl[axis] = slice(i, i + n)
            acc = ap[tuple(sl)].copy() if acc is None else np.add(acc, ap[tuple(sl)], out=acc)
        return acc / np.float32(k)
    pl = k // 2
    pw = [(0, 0)] * a.ndim
    pw[axis] = (pl, k - 1 - pl)
    ap = np.pad(a, pw, mode="edge")
    cs = np.cumsum(ap, axis=axis, dtype=np.float64)
    n = a.shape[axis]
    sl = lambda lo_, hi_: tuple(slice(lo_, hi_) if i == axis % a.ndim else slice(None) for i in range(a.ndim))
    res = cs[sl(k - 1, k - 1 + n)].copy()
    res[sl(1, n)] -= cs[sl(0, n - 1)]
    res /= k
    return res.astype(np.float32)


def band_weight(lo, hi, ramp_oct=0.5):
    f = np.maximum(FREQS, 1.0)
    up = np.clip(np.log2(f / lo) / ramp_oct + 1.0, 0, 1)
    dn = np.clip(np.log2(hi / f) / ramp_oct + 1.0, 0, 1)
    w = up * dn
    return (w * w * (3 - 2 * w)).astype(np.float32)          # smoothstep


_TB = (FREQS >= 150) & (FREQS <= 4000)


def transient_weight(mag, rise_db=9.0, breadth_min=0.75, floor_db=-30.0):
    """
    Har bir STFT kadri uchun 0..1: o'q, portlash, urilish kabi to'satdan paydo bo'ladigan
    KENG POLOSALI baland tovushmi?  Nutq (tonal, ensiz polosali) bunday deb hisoblanmaydi.
    Shart: (1) energiya oldingi ~170 ms ga nisbatan >= 9 dB oshgan, (2) chastotalarning >= 75% i
    birdan o'sgan, (3) kadr yetarli baland (> -30 dBFS).
    """
    F = mag.shape[0]
    b = mag[:, _TB].astype(np.float64)
    pw = (b * b).sum(axis=1)
    rms_db = 10 * np.log10(2 * pw / (NFFT ** 2 * 0.375) + 1e-12)
    cs = np.vstack([np.zeros((1, b.shape[1])), np.cumsum(b, axis=0)])
    t = np.arange(F)
    lo, hi = np.maximum(t - 9, 0), np.maximum(t - 1, 0)
    cnt = (hi - lo)
    prev = (cs[hi] - cs[lo]) / np.maximum(cnt, 1)[:, None]
    breadth = np.mean(b > 2.0 * prev + 1e-9, axis=1)
    rise = 10 * np.log10(pw / ((prev * prev).sum(axis=1) + 1e-12) + 1e-12)
    onset = (cnt >= 3) & (rise >= rise_db) & (breadth >= breadth_min) & (rms_db >= floor_db)
    w = np.zeros(F)
    o = onset.astype(np.float64)
    for lag in range(0, 10):                 # tovush so'nguncha ushlab turish (~200 ms)
        w[lag:] = np.maximum(w[lag:], o[:F - lag] * (1 - lag / 10.0))
    for lag in (1, 2):                       # STFT oynasi oldindan "ko'radi"
        w[:-lag] = np.maximum(w[:-lag], o[lag:] * 0.8)
    return w.astype(np.float32)


def guided_pad(st):
    return bool(st.guided)


def _frame_act(a, F):
    """Per-namuna faollik (0..1) ni STFT kadrlari markaziga o'tkazadi."""
    c = np.clip(np.arange(F) * HOP - NFFT // 2, 0, len(a) - 1)
    return a[c]


def _dip_gain(act, F, dip_db, f_lo, f_hi):
    """Dublyaj bor kadrlarda nutq diapazonini (har qanday panoramada) pasaytiruvchi (F, K) gain."""
    dg = 10 ** (-dip_db / 20.0)
    af = _frame_act(act, F)
    return 1.0 - (1.0 - dg) * af[:, None] * band_weight(f_lo, f_hi)[None, :]


def band_dip(x, act, dip_db, f_lo, f_hi):
    X = _stft(x)
    return _istft(X * _dip_gain(act, X.shape[0], dip_db, f_lo, f_hi), len(x))


def center_cancel(L, R, depth_db, f_lo, f_hi, sharp, protect=0.0, act=None, dip_db=0.0, tw=None, tw_prot=0.0):
    """
    Har bir chastotada L va R qanchalik 'bir xil' (markazda) ekanini o'lchaydi:
        c = 1 - |L-R| / (|L|+|R|)       (1 = aniq markaz, 0 = chetda / qarama-qarshi fazada)
    Markaziy komponent faqat [f_lo..f_hi] (nutq diapazoni) da pasaytiriladi, shuning uchun
    bas, kick va yuqori chastotali musiqa saqlanib qoladi.
    protect > 0 bo'lsa, o'q/portlash kabi to'satdan paydo bo'ladigan tovushlar kadrlarida
    olib tashlash kuchi kamaytiriladi.
    """
    m = len(L)
    XL, XR = _stft(L), _stft(R)
    aL, aR = np.abs(XL), np.abs(XR)
    c = 1.0 - np.abs(XL - XR) / (aL + aR + 1e-9)
    c = np.clip(c, 0, 1) ** sharp
    c = _movavg(_movavg(c, 3, 0), 3, 1)          # "musiqiy shovqin" (artefakt) ni kamaytirish
    floor = 10 ** (-depth_db / 20.0)
    k = 1.0
    if tw is not None and tw_prot > 0:                 # yon kanallardan aniqlangan effektlar (nutq boshlanishi adashtirilmaydi)
        k = 1.0 - tw_prot * _frame_act(tw, aL.shape[0])[:, None]
    elif protect > 0:
        k = 1.0 - (protect / 100.0) * transient_weight((aL + aR) * 0.5)[:, None]
    G = 1.0 - (1.0 - floor) * c * k * band_weight(f_lo, f_hi)[None, :]
    if act is not None and dip_db > 0:                 # markazda bo'lmagan ovoz uchun qo'shimcha pasaytirish
        G = G * _dip_gain(act, G.shape[0], dip_db, f_lo, f_hi)
    return _istft(XL * G, m), _istft(XR * G, m)


def _cmovavg(Z, k, axis):
    return _movavg(Z.real, k, axis) + 1j * _movavg(Z.imag, k, axis)


def leak_clean(chans, fc, strength):
    """
    FC (dialog kanali) ni andoza qilib, boshqa kanallarga sizib o'tgan SHU dialogni ayiradi:
    har bir chastota uchun kanalning FC bilan o'zaro bog'liq (korrelyatsiyalangan) qismi topiladi va
    olib tashlanadi. FC bilan bog'liq bo'lmagan musiqa va effektlar deyarli o'zgarmaydi
    (bog'liqlik past bo'lsa, ayirish ham kuchsiz).
    """
    m = len(fc)
    XF = _stft(fc)
    pf = _movavg(np.abs(XF) ** 2, 21, 0)                      # ~0.45 s vaqt bo'yicha silliqlash
    def one(x):
        X = _stft(x)
        cross = _cmovavg(X * np.conj(XF), 21, 0)
        pc = _movavg(np.abs(X) ** 2, 21, 0)
        al = cross / (pf + 1e-10)
        mag = np.abs(al)
        al = np.where(mag > 1.0, al / np.maximum(mag, 1e-12), al)
        coh2 = np.abs(cross) ** 2 / (pf * pc + 1e-20)           # 0..1: qaysi chastotada ovoz umumiy
        al = al * np.clip(coh2 * 1.5, 0, 1)
        return _istft(X - strength * al * XF, m)
    return pmap(one, chans)


NG, HG = 2048, 512                      # niqoblash uchun nozik vaqt o'lchami: oyna 43 ms, qadam 10.7 ms
WING = (0.5 - 0.5 * np.cos(2 * np.pi * np.arange(NG) / NG)).astype(np.float32)


def _stft_n(x, n=NG, hop=HG):
    m = len(x)
    total = m + 2 * n
    rem = (total - n) % hop
    if rem:
        total += hop - rem
    xp = np.zeros(total, np.float32)
    xp[n:n + m] = x
    fr = np.lib.stride_tricks.sliding_window_view(xp, n)[::hop]
    return FFT.rfft(fr * WING, axis=1)


def _istft_n(X, m, n=NG, hop=HG):
    fr = FFT.irfft(X, n=n, axis=1) * WING
    f = fr.shape[0]
    out = np.zeros((f + 3, hop), np.float64)
    for k in range(4):
        out[k:k + f] += fr[:, k * hop:(k + 1) * hop]
    return (out.reshape(-1) / 1.5)[n:n + m].astype(np.float32)


def dub_masker(dub, release_ms, look_ms=40.0):
    """
    Dublyajning vaqt-chastota "niqob" (masking) egri chizig'i: dublyaj har bir kadr va chastotada
    qanchalik baland.  Qo'shni chastotalarga yoyiladi (ovoz yaqin chastotalarni ham niqoblaydi),
    nutq tugagach release_ms davomida sekin so'nadi va nutqdan look_ms oldin boshlanadi.
    """
    D = _stft_n(dub)
    P = D.real ** 2 + D.imag ** 2
    M = np.maximum(_movavg(P, 5, 1), np.float32(0.25) * _movavg(P, 25, 1))
    hs = HG / SR
    dec = 10 ** (-6.0 * hs / max(release_ms / 1000.0, 1e-3))
    decl = 10 ** (-6.0 * hs / max(look_ms / 1000.0, 1e-3))
    for t in range(1, len(M)):
        np.maximum(M[t], M[t - 1] * dec, out=M[t])
    for t in range(len(M) - 2, -1, -1):
        np.maximum(M[t], M[t + 1] * decl, out=M[t])
    return M


def mask_clamp(x, M, r2, gfloor):
    """
    Originalni dublyaj ostiga tushirish: har bir chastota/kadrda original darajasi dublyajning
    niqob darajasidan (masofa = r2) oshmasin.  Dublyaj yo'q chastotalarda (rho=0) o'zgarmaydi,
    shuning uchun shovqin va fon saqlanadi.  Pasayish gfloor dan ko'p bo'lmaydi.
    """
    X = _stft_n(x)
    A2 = np.abs(X).astype(np.float64) ** 2
    rho = np.clip((10 * np.log10(M / (M.max() + 1e-20) + 1e-12) + 60.0) / 20.0, 0.0, 1.0)
    G = np.sqrt(np.minimum(1.0, (M * r2) / (A2 + 1e-18)))
    G = np.maximum(G, gfloor)
    G = 1.0 - rho * (1.0 - G)
    G = _movavg(_movavg(G, 3, 0), 3, 1)                 # artefaktlarni (musiqiy shovqin) silliqlash
    return _istft_n(X * G, len(x))


def mask_rho(M):
    """Dublyaj bor (rho=1) / yo'q (rho=0) chastota-vaqt joylari."""
    return np.clip((10 * np.log10(M / (M.max() + 1e-20) + 1e-12) + 60.0) / 20.0, 0.0, 1.0).astype(np.float32)


def _floor_power(P, blk=16, span=6):
    """Statsionar fon (shovqin) quvvati: har chastotada ~1.3 s oynadagi minimum (nutq so'zlar orasida
    pasayadi, shovqin esa doim turadi)."""
    F, K = P.shape
    nb = -(-F // blk)
    Pp = np.pad(P, ((0, nb * blk - F), (0, 0)), mode="edge")
    B = Pp.reshape(nb, blk, K).min(axis=1)
    Bp = np.pad(B, ((span, span), (0, 0)), mode="edge")
    N = Bp[0:nb].copy()
    for i in range(1, 2 * span + 1):
        np.minimum(N, Bp[i:i + nb], out=N)
    N = np.repeat(N, blk, axis=0)[:F]
    return _movavg(N, 5, 1)


_BAND_EDGES = np.unique(np.round(np.geomspace(100.0, 10000.0, 25) / (SR / NG)).astype(int))


def mask_bed(raw, out, M, rho, r2v, r2b, gfloor, keep, pz=None, pad_dip=0.0, spare=True, tws=None, prot=0.0):
    """
    Niqoblash + "fon saqlash" + "effekt saqlash".
      out = vokal ayirilgan signal, raw - out = ayirib olingan qism (nutq shu yerda).
    1) out dagi QOLGAN NUTQ aniqlanadi: qolgan nutq ayirilgan nutq bilan har chastota polosasida doimiy
       nisbatda bo'ladi (xona/aks-sado sizishi).  Shu nisbatdan (rho0) oshib ketgan qism (eshik yopilishi,
       qadam, zarba kabi nutqqa bog'liq bo'lmagan effekt) NUTQ EMAS deb hisoblanadi va tegilmaydi.
    2) Nutqqa tegishli qism dublyaj niqobidan (r2v) past tushiriladi (+ dublyajdan oldin/keyingi zonada pad_dip).
    3) Ayirilgan qismdan faqat statsionar fon (shovqin, ambiens) qaytariladi, dublyajdan r2b past.
    """
    Xo = _stft_n(out)
    Xd = _stft_n(raw - out)
    Ao2 = Xo.real ** 2 + Xo.imag ** 2
    Ad2 = Xd.real ** 2 + Xd.imag ** 2
    F, K = Ao2.shape
    eps = np.float32(1e-18)
    if spare:
        edges = _BAND_EDGES[_BAND_EDGES < K]
        starts = np.concatenate([[0], edges, [K]]).astype(int)
        starts = np.unique(starts)
        Pob = np.add.reduceat(_movavg(Ao2, 5, 0), starts[:-1], axis=1)
        Pdb = np.add.reduceat(_movavg(Ad2, 5, 0), starts[:-1], axis=1)
        ratio = Pob / (Pdb + eps)
        thr = np.percentile(Pdb, 60, axis=0)
        sel = Pdb > np.maximum(thr, 1e-12)
        rr = np.where(sel, ratio, np.nan)
        with np.errstate(all="ignore"):
            r0 = np.nanmedian(rr, axis=0)
        r0 = np.nan_to_num(r0, nan=0.0).astype(np.float32)
        r0k = np.repeat(r0, np.diff(starts))[:K]
        Pv = np.minimum(Ao2, np.float32(2.0) * r0k[None, :] * Ad2)       # nutqqa tegishli qism
    else:
        Pv = Ao2
    Gv = np.sqrt(np.minimum(np.float32(1.0), (M * np.float32(r2v)) / (Pv + eps)))
    np.maximum(Gv, np.float32(gfloor), out=Gv)
    Gv = 1.0 - rho * (1.0 - Gv)
    if pz is not None and pad_dip > 0:
        cen = np.clip(np.arange(F) * HG - NG // 2, 0, len(pz) - 1)
        dg = 10 ** (-pad_dip / 20.0)
        Gv = Gv * (1.0 - pz[cen][:, None] * (1.0 - np.float32(dg)))
    twm = None
    if tws is not None and prot > 0:
        cen2 = np.clip(np.arange(F) * HG - NG // 2, 0, len(tws) - 1)
        twm = (tws[cen2] * np.float32(prot))[:, None]          # (F,1): effekt kadrlari
        Gv = 1.0 - (1.0 - Gv) * (1.0 - twm)                    # effekt kadrlarida niqob kuchsizlanadi
    Gtot = np.sqrt((Pv * Gv ** 2 + (Ao2 - Pv)) / (Ao2 + eps))
    Gtot = _movavg(_movavg(Gtot, 3, 0), 3, 1)
    Y = Xo * Gtot
    if keep > 0:
        Xr = Xo + Xd
        Pr = _movavg(Xr.real ** 2 + Xr.imag ** 2, 3, 1)
        N = _floor_power(Pr) * np.float32(4.0)
        Gb = np.sqrt(np.minimum(np.float32(1.0), N / (Ad2 + eps)))
        Gb = Gb * np.sqrt(np.minimum(np.float32(1.0), (M * np.float32(r2b)) / (N + eps))) ** rho
        Gb = _movavg(_movavg(Gb, 3, 0), 3, 1) * np.float32(keep)
        Y = Y + Xd * Gb
    if twm is not None:                                         # effekt kadrlarida ayirilgan qismning ham bir qismi qaytadi
        cap = np.sqrt(np.minimum(np.float32(1.0), (M * np.float32(0.4)) / (Ad2 + eps)))
        Y = Y + Xd * (twm * (1.0 - rho * (1.0 - cap)))
    return _istft_n(Y, len(out))


class Aux:
    """Qo'shimcha oqim (dublyaj, AI natijasi): asosiy oqim bilan bir xil bo'laklar + kontekst."""

    def __init__(self, ff, ch, n0):
        self.ff, self.ch = ff, ch
        self.prev = np.zeros((CTX, ch), np.float32)
        self.cur = read_pad(ff, ch, n0)
        self.nxt = None

    def window(self, n_next):
        self.nxt = read_pad(self.ff, self.ch, n_next) if n_next > 0 else np.zeros((0, self.ch), np.float32)
        nx = self.nxt[:CTX]
        if len(nx) < CTX:
            nx = np.concatenate([nx, np.zeros((CTX - len(nx), self.ch), np.float32)])
        return np.concatenate([self.prev, self.cur, nx])

    def advance(self):
        self.prev = np.concatenate([self.prev, self.cur])[-CTX:]
        self.cur = self.nxt


def transient_samples(seg, ch):
    """
    Qisqa baland keng polosali tovushlar (eshik, zarba, qadam) uchun har bir namunadagi 0..1 vazn.
    Nutq markazda bo'lgani uchun faqat YON kanallar tahlil qilinadi (5.1: FL, FR, SL, SR; stereo: L-R);
    shunda nutq boshlanishi effekt deb adashtirilmaydi.  Mono audioda aniqlab bo'lmaydi.
    """
    if ch == 6:
        mono = seg[:, [0, 1, 4, 5]].sum(axis=1) / 2.0
    elif ch == 2:
        mono = (seg[:, 0] - seg[:, 1]) / math.sqrt(2.0)
    else:
        return None
    w = transient_weight(np.abs(_stft(mono.astype(np.float32))))
    cen = np.arange(len(w)) * HOP - NFFT // 2
    return np.interp(np.arange(len(seg)), cen, w).astype(np.float32)


def fc_transient(x, depth_db, protect):
    """5.1 FC: dialog o'chiriladi, lekin to'satdan paydo bo'lgan baland effektlar (o'q, portlash) saqlanadi."""
    m = len(x)
    X = _stft(x)
    w = transient_weight(np.abs(X)) * (protect / 100.0)
    floor = 10 ** (-depth_db / 20.0)
    G = floor + (1.0 - floor) * w[:, None]
    return _istft(X * G, m)


def soft_limit(x, th=0.95):
    ax = np.abs(x)
    over = ax > th
    n = int(over.sum())
    if n:
        x = np.where(over, np.sign(x) * (th + (1 - th) * np.tanh((ax - th) / (1 - th))), x)
    return x, n


def parse_ranges(text):
    """'12:30-12:45, 1:02:10-1:02:20' -> [(750.0, 765.0), ...] (soniya)."""
    def tsec(x):
        parts = [float(p) for p in x.strip().split(":")]
        v = 0.0
        for p_ in parts:
            v = v * 60 + p_
        return v
    out = []
    for item in re.split(r"[,;\n]+", text or ""):
        if "-" in item:
            a, b = item.split("-", 1)
            try:
                a, b = tsec(a), tsec(b)
            except ValueError:
                continue
            if b > a:
                out.append((a, b))
    return out


# ----------------------------------------------------------------------------------------
#  Sozlamalar
# ----------------------------------------------------------------------------------------
@dataclass
class Settings:
    src: str = ""
    dst: str = ""
    dub: str = ""
    stream: int = 0
    fmt: str = "WAV 24-bit (PCM)"
    mode: str = "dsp"            # dsp | ai
    ai_engine: str = "fast"      # fast | hq (MDX-Net, ONNX) | demucs
    ai_all: bool = False         # 5.1: AI old va orqa kanallarga ham (orqa fondagi gaplar uchun; sekinroq)
    vocal_cut: float = 30.0      # dB
    f_lo: float = 120.0
    f_hi: float = 9000.0
    sharp: float = 2.0
    center_cut: float = 60.0     # 5.1 markaz kanali (FC) dB
    fc_mode: str = "soft"        # soft | mute | transient | ai | keep
    fc_soft_db: float = 12.0     # "soft" rejimida FC pasayishi (dB)
    protect: float = 0.0        # effekt/zarba himoyasi %
    leak_cancel: float = 100.0   # FC dan boshqa kanallarga sizib o'tgan dialogni ayirish, %
    keep_ranges: str = ""        # himoya oraliqlari: '12:30-12:45, 1:02:10-1:02:20'
    cut_surround: bool = True
    dip_db: float = 0.0         # dublyaj bor joyda nutq diapazonini barcha kanalda qo'shimcha pasaytirish
    duck_db: float = 4.0
    mask_on: bool = True         # dublyaj spektri bo'yicha professional niqoblash
    mask_margin: float = 20.0    # original dublyajdan necha dB past bo'lsin
    mask_max_red: float = 24.0   # niqoblash beradigan maksimal pasayish (dB)
    mask_release: float = 300.0  # niqob so'nish vaqti (ms)
    pad_ms: float = 1000.0       # dublyaj atrofida (oldin va keyin) original ovozni ham yo'qotish (ms)
    side_gentle: bool = False    # 5.1: yon kanallarda (FL,FR,SL,SR) yumshoq ishlov: effektlar (eshik, qadam) saqlansin
    side_margin: float = 8.0     # shu rejimda yon kanal original dublyajdan necha dB past bo'lsin
    side_max_red: float = 12.0   # shu rejimda yon kanallarda eng ko'p pasayish (dB)
    spare_fx: bool = False       # nutqqa bog'liq bo'lmagan effektlarni (eshik, qadam) niqoblashdan ozod qilish
    pad_dip: float = 20.0        # shu atrofda nutq diapazoni pasayishi (dB)
    bed_keep: float = 85.0       # fon/shovqin saqlash (%): ayirilgan qismning shovqinsimon qismi qaytariladi
    bed_margin: float = 12.0     # fon dublyajdan necha dB past eshitilsin
    thr_db: float = -50.0
    attack: float = 30.0
    release: float = 250.0
    hold: float = 400.0
    look: float = 60.0
    bg_db: float = 0.0
    dub_db: float = 0.0
    auto_dub: bool = True        # dublyaj balandligini avtomatik moslash
    dub_target: float = -18.0    # nutq o'rtacha darajasi (dBFS)
    dub_level_up: float = 0.0    # dublyajning past (sekin) joylarini ko'tarish, eng ko'pi bilan (dB); 0 = o'chiq
    mix_dub: bool = True
    out_ch: str = "auto"         # auto | 2 | 6 : chiqish kanallari soni
    guided: bool = True          # faqat dublyaj bor joylarda original ovozni o'chirish
    test: bool = False
    test_start: float = 60.0
    test_len: float = 120.0


# ----------------------------------------------------------------------------------------
#  Asosiy ishlovchi
# ----------------------------------------------------------------------------------------
class Processor:
    def __init__(self, st, ffmpeg, ffprobe, log, progress):
        self.st = st
        self.ffmpeg, self.ffprobe = ffmpeg, ffprobe
        self.log = log
        self.progress = progress              # progress(frac 0..1 | None, matn)
        self.stop = threading.Event()
        self.procs = []
        self.tmp = None
        self._warned_mono = False
        self.t0 = time.time()

    # -- boshqaruv ---------------------------------------------------------------------
    def abort(self):
        self.stop.set()
        for p in list(self.procs):
            if isinstance(p, FF):
                p.kill()
            else:
                try:
                    p.kill()
                except Exception:
                    pass

    def _chk(self):
        if self.stop.is_set():
            raise Cancelled()

    def _ff(self, cmd, **kw):
        f = FF(cmd, **kw)
        self.procs.append(f)
        return f

    def _prog(self, base, weight, frac, label):
        frac = min(max(frac, 0.0), 1.0)
        total = base + weight * frac
        self.progress(total, label)

    # -- ffmpeg buyruqlari -------------------------------------------------------------
    def _in_opts(self):
        st = self.st
        return ["-ss", f"{st.test_start:.3f}", "-t", f"{st.test_len:.3f}"] if st.test else []

    def _decode_cmd(self, path, ch_arg, rate, stream_rel=None, in_opts=True):
        cmd = [self.ffmpeg, "-hide_banner", "-v", "error", "-nostdin"]
        if in_opts:
            cmd += self._in_opts()
        cmd += ["-i", path]
        if stream_rel is not None:
            cmd += ["-map", f"0:a:{stream_rel}"]
        cmd += ["-vn", "-sn", "-dn"]
        if ch_arg:
            cmd += ["-ac", str(ch_arg)]
        cmd += ["-ar", str(rate), "-f", "f32le", "-acodec", "pcm_f32le", "-"]
        return cmd

    def _encode_cmd(self, ch, out_path, video_src):
        st = self.st
        f = FORMATS[st.fmt]
        kind = f["kind"]
        cmd = [self.ffmpeg, "-hide_banner", "-v", "error", "-y", "-nostdin"]
        if video_src:
            cmd += ["-i", video_src]
        cmd += ["-f", "f32le", "-ar", str(SR), "-ac", str(ch), "-i", "pipe:0"]
        if video_src:
            cmd += ["-map", "0:v:0", "-map", "1:a:0", "-c:v", "copy"]
        och = 2 if (ch == 6 and st.out_ch == "2") else ch
        if och != ch:       # 5.1 -> 2.0 (dublyaj FC da: yetarli balandlikda qoladi, limiter bilan)
            cmd += ["-af", "pan=stereo|c0=0.7*c0+0.9*c2+0.5*c4+0.2*c3|c1=0.7*c1+0.9*c2+0.5*c5+0.2*c3,"
                           "alimiter=limit=0.97:level=disabled"]
        br = {6: ("640k", "768k", "512k"), 2: ("448k", "256k", "256k"), 1: ("192k", "128k", "128k")}[och]
        if kind == "wav":
            cmd += ["-c:a", "pcm_s24le", "-rf64", "auto"]
        elif kind == "flac":
            cmd += ["-c:a", "flac", "-compression_level", "5"]
        elif kind == "ac3":
            cmd += ["-c:a", "ac3", "-b:a", br[0]]
        elif kind == "eac3":
            cmd += ["-c:a", "eac3", "-b:a", br[1]]
        elif kind == "aac":
            cmd += ["-c:a", "aac", "-b:a", br[2]]
        elif kind == "mp3":
            cmd += ["-c:a", "libmp3lame", "-b:a", "320k"]
            if ch > 2:
                cmd += ["-ac", "2"]
        if video_src:
            cmd += ["-metadata:s:a:0", "language=uzb", "-metadata:s:a:0", "title=Uzbek dublyaj"]
        cmd += [out_path]
        return cmd

    # -- 1-bosqich: Demucs (ixtiyoriy) --------------------------------------------------
    def _run_demucs(self, ch_in, ch, base, weight, kind="front"):
        st = self.st
        self.log("AI: Demucs bilan " + ("markaz kanal (FC)" if kind == "fc" else "old kanallar") +
                 " tozalanmoqda (bu uzoq davom etishi mumkin)...")
        front = os.path.join(self.tmp, kind + ".wav")
        cmd = [self.ffmpeg, "-hide_banner", "-v", "error", "-y", "-nostdin"] + self._in_opts()
        cmd += ["-i", st.src, "-map", f"0:a:{st.stream}", "-vn"]
        if kind == "fc":
            cmd += ["-af", "pan=stereo|c0=c2|c1=c2"]
        elif ch == 6:
            cmd += ["-af", "pan=stereo|c0=c0|c1=c1"]
        elif ch == 1:
            cmd += ["-ac", "2"]
        cmd += ["-ar", "44100", "-c:a", "pcm_s24le", front]
        f = self._ff(cmd)
        if f.finish() != 0:
            raise RuntimeError("Demucs uchun audio ajratib bo'lmadi:\n" + f.tail())
        self._chk()
        out_dir = os.path.join(self.tmp, "sep")
        dcmd = [sys.executable, "-m", "demucs", "--two-stems=vocals", "-n", "htdemucs",
                "--int24", "-o", out_dir, front]
        p = subprocess.Popen(dcmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                             creationflags=_flags())
        self.procs.append(p)
        last, tail = -1, collections.deque(maxlen=15)
        buf = b""
        while True:
            chunk = p.stderr.read(256)
            if not chunk:
                break
            buf = (buf + chunk)[-400:]
            txt = buf.decode("utf-8", "replace")
            tail.append(txt[-120:])
            m = re.findall(r"(\d{1,3})%", txt)
            if m:
                pct = min(int(m[-1]), 100)
                if pct != last:
                    last = pct
                    self._prog(base, weight, pct / 100.0, f"Demucs ({kind}): {pct}%")
            self._chk()
        if p.wait() != 0:
            raise RuntimeError("Demucs xatosi:\n" + "".join(tail)[-500:])
        res = os.path.join(out_dir, "htdemucs", kind, "no_vocals.wav")
        if not os.path.isfile(res):
            raise RuntimeError("Demucs natija faylini topib bo'lmadi: " + res)
        self.log("Demucs tugadi.")
        return res

    # -- 1-bosqich (tez): MDX-Net, faqat dublyaj bor joylarda -----------------------------
    def _active_blocks(self, nblocks, blk, margin=1.0):
        """Har bir blok (blk namuna @44.1k) uchun: dublyaj (kengaytirilgan) faolmi? env 10 ms kadrlarda."""
        env = getattr(self, "env_wide", None)
        if env is None:
            env = getattr(self, "env_now", None)
        if env is None or not self.st.guided:
            return np.ones(nblocks, bool)
        res = np.zeros(nblocks, bool)
        for i in range(nblocks):
            t0 = i * blk / MDX_SR - margin
            t1 = (i + 1) * blk / MDX_SR + margin
            a, b = max(int(t0 / ENV_HOP), 0), int(t1 / ENV_HOP) + 1
            res[i] = bool(np.any(env[a:b] > 1e-3)) if a < len(env) else False
        return res

    def _run_mdx(self, ch_in, ch, base, weight, kind, mdx):
        st = self.st
        self.log("AI (MDX-Net): " + {"fc": "markaz kanal (FC)", "rear": "orqa (surround) kanallar"}.get(kind, "old kanallar") +
                 f" tozalanmoqda [{mdx.prov.replace('ExecutionProvider', '')}]...")
        cmd = [self.ffmpeg, "-hide_banner", "-v", "error", "-nostdin"] + self._in_opts()
        cmd += ["-i", st.src, "-map", f"0:a:{st.stream}", "-vn"]
        if kind == "fc":
            cmd += ["-af", "pan=stereo|c0=c2|c1=c2"]
        elif kind == "rear":
            cmd += ["-af", "pan=stereo|c0=c4|c1=c5"]
        elif ch_in == 6:
            cmd += ["-af", "pan=stereo|c0=c0|c1=c1"]
        else:
            cmd += ["-ac", "2"]
        cmd += ["-ar", str(MDX_SR), "-f", "f32le", "-acodec", "pcm_f32le", "-"]
        rd = self._ff(cmd, stdout=True)
        K = mdx.chunk - 2 * (mdx.n_fft // 2)           # chetlari kesiladi (STFT chekka effekti)
        trim = mdx.n_fft // 2
        total = float(getattr(self, "total_sec", 0) or 0)
        nblocks = int(total * MDX_SR / K) + 2 if total else 0
        act = self._active_blocks(nblocks, K) if nblocks else None
        out_path = os.path.join(self.tmp, kind + ".f32")
        zero = np.zeros((trim, 2), np.float32)
        t0 = time.time()
        done = skipped = 0
        N = max(mdx.n, 1)
        bl, eof = [], False
        prevtail = zero
        i = 0
        with open(out_path, "wb") as fo:
            while True:
                self._chk()
                while not eof and len(bl) < N + 1:
                    b = read_n(rd, 2, K)
                    if len(b) == 0:
                        eof = True
                    else:
                        bl.append(b)
                        eof = len(b) < K
                if not bl:
                    break
                grp = bl[:N]
                jobs, idxs, xs = [], [], []
                for j, cur in enumerate(grp):
                    use = True if act is None or (i + j) >= len(act) else bool(act[i + j])
                    if use:
                        pt = prevtail if j == 0 else grp[j - 1][-trim:]
                        nxh = bl[j + 1][:trim] if j + 1 < len(bl) else np.zeros((0, 2), np.float32)
                        xs.append(np.concatenate([pt, cur, nxh,
                                                  np.zeros((mdx.chunk - len(pt) - len(cur) - len(nxh), 2), np.float32)]))
                        idxs.append(j)
                vs = mdx.vocals_many(xs) if xs else []
                vmap = {j: v for j, v in zip(idxs, vs)}
                for j, cur in enumerate(grp):
                    if j in vmap:
                        fo.write(np.ascontiguousarray(cur - vmap[j][trim:trim + len(cur)], dtype="<f4").tobytes())
                        done += 1
                    else:
                        fo.write(np.ascontiguousarray(cur, dtype="<f4").tobytes())
                        skipped += 1
                prevtail = grp[-1][-trim:] if len(grp[-1]) >= trim else np.concatenate([prevtail, grp[-1]])[-trim:]
                i += len(grp)
                del bl[:len(grp)]
                nb = max(nblocks, i)
                el = time.time() - t0
                eta = ""
                if done and nblocks:
                    left_active = int(np.sum(act[i:])) if act is not None and i < len(act) else 0
                    eta = f" | qoldi ~{fmt_time(el / done * left_active)}"
                self._prog(base, weight, i / max(nb, 1), f"AI ({kind}): {100 * i // max(nb, 1)}%{eta}")
        rd.finish()
        self.log(f"AI tugadi: {fmt_time(time.time() - t0)} ({done} bo'lak ishlandi, {skipped} bo'lak dublyajsiz — o'tkazildi).")
        return out_path

    # -- 2-bosqich: dublyaj bo'yicha ducking egri chizig'i -------------------------------
    def _duck_curve(self, base, weight):
        st = self.st
        self.log("Dublyaj ovozi tahlil qilinmoqda (ducking egri chizig'i)...")
        f = self._ff(self._decode_cmd(st.dub, 1, ENV_SR), stdout=True)
        fl = int(ENV_SR * ENV_HOP)                  # 160 namuna = 10 ms
        per = fl * 6000                              # ~1 daqiqa
        db_list = []
        self.dub_peak_db = -120.0
        self.dub_level_db = None
        while True:
            self._chk()
            a = read_n(f, 1, per)
            if len(a) == 0:
                break
            self.dub_peak_db = max(self.dub_peak_db, 20 * math.log10(float(np.abs(a).max()) + 1e-9))
            n = (len(a) // fl) * fl
            if n < len(a):                           # oxirgi to'liqmas kadr
                a = np.concatenate([a[:, 0], np.zeros(fl - (len(a) - n), np.float32)])
            else:
                a = a[:, 0]
            rms = np.sqrt(np.mean(a.reshape(-1, fl).astype(np.float64) ** 2, axis=1))
            db_list.append(20 * np.log10(rms + 1e-9))
            self._prog(base, weight, 0.5, "Dublyaj tahlili...")
            if len(a) < per:
                break
        f.finish()
        if not db_list:
            raise RuntimeError("Dublyaj faylidan audio o'qib bo'lmadi.")
        db = np.concatenate(db_list)
        nfr = len(db)
        thr = st.thr_db
        voiced = db[db > -80]
        if len(voiced) > 100:
            ref = float(np.percentile(voiced, 95))
            if ref < -30 and ref - 30 < thr:             # juda past dublyaj: sezgirlikni oshiramiz
                thr = max(ref - 30, -75.0)
                self.log(f"Dublyaj juda past (cho'qqi ~{ref:.0f} dBFS): bo'sag'a {st.thr_db:.0f} -> {thr:.0f} dB.")
        act = db > thr
        # hold (oldinga) va lookahead (orqaga) - dilatatsiya
        hold = int(round(st.hold / 1000 / ENV_HOP))
        look = int(round(st.look / 1000 / ENV_HOP))
        cs = np.concatenate([[0], np.cumsum(act, dtype=np.int64)])
        idx = np.arange(nfr)
        hi = np.minimum(idx + look + 1, nfr)
        lo = np.maximum(idx - hold, 0)
        tgt_on = (cs[hi] - cs[lo]) > 0
        a_att = 1 - math.exp(-ENV_HOP / max(st.attack / 1000, 1e-4))
        a_rel = 1 - math.exp(-ENV_HOP / max(st.release / 1000, 1e-4))
        env = np.empty(nfr, np.float32)          # 0 = dublyaj yo'q, 1 = dublyaj bor (silliq o'tish bilan)
        g = 0.0
        for i, t in enumerate(tgt_on.tolist()):
            g += (t - g) * (a_att if t > g else a_rel)
            env[i] = g
        if act.any():
            self.dub_level_db = 10 * math.log10(float(np.mean(10 ** (db[act] / 10.0))) + 1e-12)
        self.dub_lev = None
        if st.dub_level_up > 0 and act.any():
            self.dub_lev = self._leveler(db, act, st.dub_level_up, nfr)
        self.env_wide = env
        if st.pad_ms > 0 and guided_pad(st):
            pad = int(round(st.pad_ms / 1000 / ENV_HOP))
            hi2 = np.minimum(idx + look + pad + 1, nfr)
            lo2 = np.maximum(idx - hold - pad, 0)
            tgt2 = (cs[hi2] - cs[lo2]) > 0
            ew = np.empty(nfr, np.float32)
            g = 0.0
            for i, t in enumerate(tgt2.tolist()):
                g += (t - g) * (a_att if t > g else a_rel)
                ew[i] = g
            self.env_wide = np.maximum(ew, env)
        pct = 100.0 * float(np.mean(tgt_on))
        self.log(f"Dublyaj bor joylar: {pct:.1f}% ({fmt_time(pct / 100 * nfr * ENV_HOP)} dan "
                 f"{fmt_time(nfr * ENV_HOP)})")
        self.progress(base + weight, "Dublyaj tahlili tugadi")
        return env

    def _leveler(self, db, act, up, nfr):
        """Dublyajning nutq bor, lekin o'rtachadan past joylariga silliq ko'tarish (chiziqli gain, kadr = 10 ms)."""
        a = act.astype(np.float64)
        p = (10 ** (db / 10.0)) * a
        w = 30                                              # ~300 ms
        k = np.ones(w) / w
        num = np.convolve(p, k, "same")
        den = np.convolve(a, k, "same")
        lvl = 10 * np.log10(num / np.maximum(den, 1e-9) + 1e-12)
        ref = (self.dub_level_db if self.dub_level_db is not None else float(np.mean(db[act]))) - 1.5
        g = np.clip(ref - lvl, 0.0, up)
        g[den < 0.15] = 0.0                                 # nutq deyarli yo'q joyda ko'tarilmaydi
        for ord_ in (1, -1):                                # nol-fazali silliqlash (oldinga va orqaga)
            c = 0.0
            al = 1 - math.exp(-ENV_HOP / 0.15)
            rng = range(nfr) if ord_ == 1 else range(nfr - 1, -1, -1)
            for i in rng:
                c += (g[i] - c) * al
                g[i] = c
        self.log(f"Dublyaj past joylari ko'tariladi (eng ko'pi bilan +{up:.0f} dB, o'rtacha +{float(np.mean(g[act])):.1f} dB).")
        return (10 ** (g / 20.0)).astype(np.float32)

    # -- DSP bo'lagi -------------------------------------------------------------------
    def _mask(self, out, dub, ch, raw=None, pz=None, tws=None):
        st = self.st
        M = dub_masker(dub, st.mask_release)
        rho = mask_rho(M)
        r2 = 10 ** (-st.mask_margin / 10.0)
        r2b = 10 ** (-st.bed_margin / 10.0)
        gfloor = 10 ** (-st.mask_max_red / 20.0)
        keep = st.bed_keep / 100.0
        chans = {6: [0, 1, 2, 4, 5], 2: [0, 1], 1: [0]}.get(ch, [])

        def one(c):
            # 5.1 da dublyaj FC dan chiqadi: boshqa kanallar fazoviy ajralgan, ularga kamroq talab
            rc = r2 * (10 ** 0.8 if (ch == 6 and c != 2) else 1.0)
            gf, pzc = gfloor, pz
            if ch == 6 and c != 2 and st.side_gentle:
                rc = 10 ** (-st.side_margin / 10.0)
                gf = 10 ** (-st.side_max_red / 20.0)
                pzc = None                                   # yon kanallarda dublyaj atrofi pasaytirilmaydi
            if raw is not None:
                return mask_bed(raw[:, c], out[:, c], M, rho, rc, r2b, gf, keep * (0.5 if c == 2 else 1.0),
                                pzc, st.pad_dip, st.spare_fx, tws, st.protect / 100.0)
            return mask_clamp(out[:, c], M, rc, gfloor)
        for c, y in zip(chans, pmap(one, chans)):
            out[:, c] = y
        return out

    def _process_segment(self, seg, ch, ai, act=None, aux=None):
        """seg: (M, ch). act: har namuna uchun dublyaj faolligi (0..1) yoki None (butun film rejimi)."""
        st = self.st
        raw = seg
        out = seg.copy()
        tws = None
        if act is not None and st.protect > 0:
            tws = transient_samples(seg, ch)
        dip = st.dip_db if act is not None else 0.0
        if ch == 6 and st.side_gentle:
            dip = 0.0
        act_dip = act if (tws is None or act is None) else act * (1.0 - tws * (st.protect / 100.0))
        if ch == 6 and st.leak_cancel > 0:
            cl = leak_clean([seg[:, 0], seg[:, 1], seg[:, 4], seg[:, 5]], seg[:, 2], st.leak_cancel / 100.0)
            seg = seg.copy()
            for c_, y_ in zip((0, 1, 4, 5), cl):
                seg[:, c_] = y_
            out = seg.copy()
            out[:, 2] = seg[:, 2]
        pairs, singles = [], []
        if ch == 2:
            if not ai:
                pairs.append((0, 1))
        elif ch == 6:
            if not ai:
                pairs.append((0, 1))
            if st.cut_surround:
                pairs.append((4, 5))
            else:
                singles += [4, 5]
            if st.fc_mode == "soft" and act is not None:
                if tws is not None:                      # effekt (eshik, zarba) paytida FC pasaytirish kamayadi
                    out[:, 2] *= (10 ** (-st.fc_soft_db / 20.0)) ** (1.0 - tws * (st.protect / 100.0))
                else:
                    out[:, 2] *= 10 ** (-st.fc_soft_db / 20.0)
            elif st.fc_mode in ("mute", "soft") or (st.fc_mode == "transient" and st.protect <= 0):
                out[:, 2] *= 10 ** (-st.center_cut / 20.0)
            elif st.fc_mode == "transient":
                out[:, 2] = fc_transient(seg[:, 2], st.center_cut, st.protect)
            elif st.fc_mode == "keep":
                singles.append(2)
            # "ai" - Demucs natijasi keyin qo'yiladi
        elif ch == 1:
            if not ai:
                singles.append(0)
                if act is None and not self._warned_mono:
                    self._warned_mono = True
                    self.log("DIQQAT: original MONO. Mono audiodan vokalni faza usuli bilan ajratib bo'lmaydi. "
                             "'Dublyaj bo'yicha' rejimi (nutq diapazonini pasaytirish) yoki AI (Demucs) tavsiya etiladi.")
        def cc(pr):
            return center_cancel(seg[:, pr[0]], seg[:, pr[1]], st.vocal_cut, st.f_lo, st.f_hi, st.sharp,
                                 st.protect, act_dip, dip, tws, st.protect / 100.0)
        for (a_, b_), (l, r) in zip(pairs, pmap(cc, pairs)):
            out[:, a_], out[:, b_] = l, r
        if act is not None and dip > 0:
            for c_ in singles:
                out[:, c_] = band_dip(seg[:, c_], act_dip, dip, st.f_lo, st.f_hi)
        if aux:
            if "ai" in aux:                                  # Demucs natijasi (kontekst bilan)
                v = aux["ai"]
                if ch == 1:
                    out[:, 0] = v.mean(axis=1)
                else:
                    out[:, 0:2] = v
            if "fc" in aux and ch == 6:
                out[:, 2] = aux["fc"].mean(axis=1)
            if "rear" in aux and ch == 6:
                out[:, 4:6] = aux["rear"]
            pz = aux.get("padz")
            if pz is not None and tws is not None:
                pz = pz * (1.0 - tws * (st.protect / 100.0))
            if pz is not None and st.pad_dip > 0 and pz.max() > 0.01 and not ("dub" in aux and st.mask_on):
                # dublyajdan oldin/keyin: asl nutq bor, lekin niqoblovchi dublyaj yo'q -> nutq diapazonini kuchli pasaytiramiz
                cl = {6: [0, 1, 2, 4, 5], 2: [0, 1], 1: [0]}.get(ch, [])
                for c_, y_ in zip(cl, pmap(lambda c: band_dip(out[:, c], pz, st.pad_dip, st.f_lo, st.f_hi), cl)):
                    out[:, c_] = y_
            if "dub" in aux and st.mask_on and act is not None:
                out = self._mask(out, aux["dub"], ch, raw, pz, tws)
        return out

    # -- Asosiy ish --------------------------------------------------------------------
    def run(self):
        st = self.st
        ok, msg = False, ""
        out_tmp = None
        try:
            self.t0 = time.time()
            lic_require()
            if not self.ffmpeg or not self.ffprobe:
                raise RuntimeError("FFmpeg/FFprobe topilmadi.")
            if not os.path.isfile(st.src):
                raise RuntimeError("Original fayl topilmadi.")
            if st.dub and not os.path.isfile(st.dub):
                raise RuntimeError("Dublyaj fayli topilmadi.")
            if not st.dst:
                raise RuntimeError("Saqlash joyi ko'rsatilmagan.")
            fmt = FORMATS[st.fmt]
            use_video = fmt.get("video", False) and not st.test
            if fmt.get("video") and st.test:
                self.log("Sinov rejimi: video qo'shilmaydi, faqat audio saqlanadi (.wav).")
                st.dst = os.path.splitext(st.dst)[0] + ".wav"
                st.fmt = "WAV 24-bit (PCM)"

            info = probe(self.ffprobe, st.src)
            if not info["audio"]:
                raise RuntimeError("Faylda audio oqim topilmadi.")
            if st.stream >= len(info["audio"]):
                st.stream = 0
            a = info["audio"][st.stream]
            if use_video and not info["has_video"]:
                raise RuntimeError("Tanlangan format video talab qiladi, lekin original faylda video yo'q.")

            ch_in = a["channels"]
            ch = ch_in if ch_in in (1, 2, 6) else 6
            ch_arg = None if ch == ch_in else ch
            if st.out_ch == "6" and ch != 6:
                self.log("Eslatma: original 5.1 emas, shuning uchun chiqish asl kanallar sonida saqlanadi.")
            elif st.out_ch == "2" and ch == 6:
                self.log("Chiqish: 5.1 dan Stereo (2.0) ga aralashtiriladi.")
            total = float(a["duration"] or info["duration"] or 0)
            if st.test:
                total = min(st.test_len, max(total - st.test_start, 0)) if total else st.test_len
            self.log(f"Original: {os.path.basename(st.src)}")
            self.log(f"Audio oqim: {describe_stream(a)}")
            if ch != ch_in:
                self.log(f"{ch_in} kanal -> {ch} kanalga o'tkazilmoqda (FFmpeg orqali).")
            eng = st.ai_engine if st.ai_engine in ("fast", "hq", "demucs") else "fast"
            eng_txt = {"fast": "AI (MDX-Net, tez)", "hq": "AI (MDX-Net, sifatli)", "demucs": "AI (Demucs)"}[eng]
            mode_txt = eng_txt if st.mode == "ai" else "DSP (spektral markaz o'chirish)"
            self.total_sec = total
            self.log(f"Rejim: {mode_txt}  |  "
                     f"chiqish: {ch} kanal, {SR} Hz  |  uzunlik: {fmt_time(total) if total else '?'}"
                     + ("  |  SINOV REJIMI" if st.test else ""))

            ai = st.mode == "ai"
            guided = bool(st.guided and st.dub)
            if st.guided and not st.dub:
                self.log("Dublyaj fayli yo'q -> avtomatik rejim ishlamaydi, butun film bo'ylab vokal o'chiriladi.")
            self.log("Rejim: " + ("DUBLYAJ BO'YICHA — original faqat dublyaj bor joylarda o'chiriladi, qolgan joylar o'zgarishsiz"
                                 if guided else "BUTUN FILM — hamma joyda vokal o'chiriladi"))
            if ai and eng != "demucs" and importlib.util.find_spec("onnxruntime") is None:
                if importlib.util.find_spec("demucs") is not None:
                    self.log("onnxruntime o'rnatilmagan (pip install onnxruntime) -> Demucs ishlatiladi (sekinroq).")
                    eng = "demucs"
                else:
                    self.log("onnxruntime o'rnatilmagan (pip install onnxruntime) -> DSP rejimiga o'tildi.")
                    ai = False
            elif ai and eng == "demucs" and importlib.util.find_spec("demucs") is None:
                self.log("Demucs o'rnatilmagan (pip install demucs) -> DSP rejimiga o'tildi.")
                ai = False
            have_dub = bool(st.dub)
            dub_ch_in = 0
            if have_dub:
                di = probe(self.ffprobe, st.dub)
                if not di["audio"]:
                    raise RuntimeError("Dublyaj faylida audio topilmadi.")
                dub_ch_in = di["audio"][0]["channels"]
                self.log(f"Dublyaj: {os.path.basename(st.dub)} ({dub_ch_in} kanal)")
            else:
                self.log("Dublyaj fayli berilmagan: faqat vokalsiz FON (M&E) tayyorlanadi.")

            fc_ai = ai and ch == 6 and st.fc_mode == "ai"
            if st.fc_mode == "ai" and not fc_ai and ch == 6:
                self.log("FC uchun AI faqat 'AI (Demucs)' rejimida ishlaydi -> to'liq o'chirish ishlatiladi.")
                st.fc_mode = "mute"
            ranges = parse_ranges(st.keep_ranges)
            if st.test:
                ranges = [(a0 - st.test_start, b0 - st.test_start) for a0, b0 in ranges]
            if ranges:
                self.log(f"Himoya oraliqlari (asl ovoz o'zgarishsiz): {len(ranges)} ta")
            w_ai = (0.55 if eng == "demucs" else 0.70) if ai else 0.0
            w_duck = 0.04 if have_dub else 0.0
            w_main = 1.0 - w_ai - w_duck

            if ai:
                self.tmp = tempfile.mkdtemp(prefix="dublyaj_", dir=os.path.dirname(os.path.abspath(st.dst)) or None)

            ai_file = fc_file = rear_file = None
            ai_front = ai
            rear_ai = False
            raw_ai = False
            # dublyaj tahlili AI dan OLDIN: AI faqat dublyaj bor joylarda ishlaydi
            env = self._duck_curve(0.0, w_duck) if w_duck else None
            self._chk()
            if ai and eng != "demucs":
                raw_ai = True
                rear_ai = ch == 6 and st.ai_all
                if fc_ai and not st.ai_all:
                    ai_front = False         # 5.1: old kanallar DSP bilan, faqat markaz (FC) AI bilan -> tezroq
                    self.log("Tezlik uchun: 5.1 da AI faqat markaz kanal (dialog) uchun ishlaydi.")
                elif rear_ai:
                    self.log("5.1: AI markaz, old va orqa kanallarga ishlaydi (orqa fondagi gaplar ham o'chadi, sekinroq).")
                if not mdx_have(eng):
                    self.log("Birinchi marta: AI modeli yuklab olinadi (internet kerak)...")
                try:
                    mdx = MDX(eng, self.log)
                except Exception as e:                       # noqa
                    mdx = None
                    self.log(f"AI ishga tushmadi: {str(e)[:300]}")
                    self.log("Ehtimoliy sabab: Windows'da 'Microsoft Visual C++ Redistributable (x64)' yo'q yoki eski. "
                             "EXE papkasidagi vc_redist.x64.exe ni o'rnating. Hozircha DSP rejimida davom etiladi.")
                    w_main += w_ai
                    w_ai = 0.0
                    ai = ai_front = fc_ai = rear_ai = raw_ai = False
                    if st.fc_mode == "ai":
                        st.fc_mode = "mute"
                if mdx is not None:
                    self.log(f"AI qurilma: {mdx.prov.replace('ExecutionProvider', '')}, "
                             f"oqimlar: {max(1, os.cpu_count() or 2)}")
                    steps = [k for k, on in (("front", ai_front), ("fc", fc_ai), ("rear", rear_ai)) if on]
                    share = w_ai / max(len(steps), 1)
                    for j, kind in enumerate(steps):
                        f_ = self._run_mdx(ch_in, ch, w_duck + j * share, share, kind, mdx)
                        if kind == "fc":
                            fc_file = f_
                        elif kind == "rear":
                            rear_file = f_
                        else:
                            ai_file = f_
                    del mdx
            elif ai:
                share = w_ai / (2 if fc_ai else 1)
                ai_file = self._run_demucs(ch_in, ch, w_duck, share, "front")
                if fc_ai:
                    self._chk()
                    fc_file = self._run_demucs(ch_in, ch, w_duck + share, share, "fc")
            self._chk()

            # dublyajni chiqish kanallariga moslash
            if have_dub and st.mix_dub:
                if ch == 6:
                    dch = 6 if dub_ch_in == 6 else 1
                elif ch == 2:
                    dch = 1 if dub_ch_in == 1 else 2
                else:
                    dch = 1
            else:
                dch = 0

            # oqimlarni ochish
            self.log("Ishlov boshlandi...")
            main = self._ff(self._decode_cmd(st.src, ch_arg, SR, stream_rel=st.stream), stdout=True)
            dubr = self._ff(self._decode_cmd(st.dub, dch, SR), stdout=True) if dch else None
            rawin = ["-f", "f32le", "-ar", str(MDX_SR), "-ac", "2"] if raw_ai else []
            air = self._ff([self.ffmpeg, "-hide_banner", "-v", "error", "-nostdin"] + rawin + ["-i", ai_file,
                            "-vn", "-ar", str(SR), "-ac", "2", "-f", "f32le", "-acodec", "pcm_f32le", "-"],
                           stdout=True) if ai_file else None
            dubm = self._ff(self._decode_cmd(st.dub, 1, SR), stdout=True) if (guided and st.mask_on) else None
            fcr = self._ff([self.ffmpeg, "-hide_banner", "-v", "error", "-nostdin"] + rawin + ["-i", fc_file,
                            "-vn", "-ar", str(SR), "-ac", "2", "-f", "f32le", "-acodec", "pcm_f32le", "-"],
                           stdout=True) if fc_file else None
            rr_ = self._ff([self.ffmpeg, "-hide_banner", "-v", "error", "-nostdin"] + rawin + ["-i", rear_file,
                           "-vn", "-ar", str(SR), "-ac", "2", "-f", "f32le", "-acodec", "pcm_f32le", "-"],
                           stdout=True) if rear_file else None
            out_tmp = st.dst
            writer = self._ff(self._encode_cmd(ch, st.dst, st.src if use_video else None), stdin=True)

            S = SEG_SEC * SR
            bg_gain = 10 ** (st.bg_db / 20.0)
            auto_db = 0.0
            if dch and st.auto_dub and getattr(self, "dub_level_db", None) is not None:
                auto_db = st.dub_target - self.dub_level_db            # nutq darajasini maqsadga keltirish
                auto_db = min(auto_db, 3.0 - self.dub_peak_db)         # cho'qqi limiterdan ko'p oshmasin
                auto_db = max(-12.0, min(auto_db, 24.0))
                self.log(f"Dublyaj balandligi: nutq {self.dub_level_db:.1f} dBFS -> maqsad {st.dub_target:.0f} dBFS "
                         f"(avtomatik {auto_db:+.1f} dB" + (f", qo'lda {st.dub_db:+.1f} dB" if st.dub_db else "") + ")")
            dub_gain = 10 ** ((st.dub_db + auto_db) / 20.0)
            cur = read_n(main, ch, S)
            if len(cur) == 0:
                raise RuntimeError("Original audioni o'qib bo'lmadi:\n" + main.tail())
            prev = np.zeros((CTX, ch), np.float32)
            dax = Aux(dubm, 1, len(cur)) if dubm else None
            aix = Aux(air, 2, len(cur)) if air else None
            fcx = Aux(fcr, 2, len(cur)) if fcr else None
            rrx = Aux(rr_, 2, len(cur)) if rr_ else None
            pos, peak, clipped = 0, 0.0, 0
            e_in, e_out = np.zeros(ch), np.zeros(ch)
            tstart = time.time()

            while True:
                self._chk()
                nxt = read_n(main, ch, S) if len(cur) == S else np.zeros((0, ch), np.float32)
                nx = nxt[:CTX]
                if len(nx) < CTX:
                    nx = np.concatenate([nx, np.zeros((CTX - len(nx), ch), np.float32)])
                n = len(cur)
                a = a_full = aw = aw_full = None
                lev_full = lev_seg = None
                if env is not None:
                    tf = np.maximum(pos - CTX + np.arange(n + 2 * CTX), 0) / SR / ENV_HOP
                    a_full = np.interp(tf, np.arange(len(env)), env).astype(np.float32)
                    a = a_full[CTX:CTX + n]
                    aw_full, aw = a_full, a
                    if getattr(self, "dub_lev", None) is not None:
                        lev_full = np.interp(tf, np.arange(len(self.dub_lev)), self.dub_lev).astype(np.float32)
                        lev_seg = lev_full[CTX:CTX + n]
                    if guided and getattr(self, "env_wide", None) is not None:
                        aw_full = np.interp(tf, np.arange(len(self.env_wide)), self.env_wide).astype(np.float32)
                        aw = aw_full[CTX:CTX + n]
                auxd = {}
                if dax:
                    auxd["dub"] = dax.window(len(nxt))[:, 0] * dub_gain
                    if lev_full is not None:
                        auxd["dub"] = auxd["dub"] * lev_full[:len(auxd["dub"])]
                if aix:
                    auxd["ai"] = aix.window(len(nxt))
                if fcx:
                    auxd["fc"] = fcx.window(len(nxt))
                if rrx:
                    auxd["rear"] = rrx.window(len(nxt))
                if guided and aw.max() < 1e-3:                  # bu bo'lakda dublyaj yo'q: tegmaymiz
                    core = cur.copy()
                    skip = True
                else:
                    skip = False
                    full = np.concatenate([prev, cur, nx])
                    if guided:
                        auxd["padz"] = np.clip(aw_full - a_full, 0, 1)
                    proc = self._process_segment(full, ch, ai_front, aw_full if guided else None, auxd)
                    core = np.array(proc[CTX:CTX + len(cur)])

                if ranges:                                   # himoya oraliqlari: asl ovoz
                    pm = np.zeros(n, np.float32)
                    for a0, b0 in ranges:
                        i0, i1 = int((a0 * SR) - pos), int((b0 * SR) - pos)
                        if i1 > 0 and i0 < n:
                            pm[max(i0, 0):min(i1, n)] = 1.0
                    if pm.any():
                        pm = _movavg(pm, int(0.25 * SR), 0)       # 250 ms silliq o'tish
                        core = core * (1 - pm[:, None]) + cur * pm[:, None]

                dk = 10 ** (-st.duck_db / 20.0)
                if guided:
                    if not skip:                          # dublyaj bor joyda: ishlangan, pasaytirilgan fon;
                        awm = aw[:, None]                 # yo'q joyda: asl ovoz (silliq o'tish bilan)
                        dkm = 1.0 - (1.0 - dk) * a[:, None]      # fon pasayishi faqat dublyaj ichida
                        core = cur * (1 - awm) + core * (awm * dkm * bg_gain)
                else:
                    gain = np.full(n, bg_gain, np.float32)
                    if a is not None:
                        gain *= 1.0 - (1.0 - dk) * a
                    core *= gain[:, None]

                if a is not None:                          # diagnostika: dublyaj joylarida har bir kanal pasayishi
                    mk = a > 0.9
                    if mk.any():
                        e_in += np.sum(cur[mk].astype(np.float64) ** 2, axis=0)
                        e_out += np.sum(core[mk].astype(np.float64) ** 2, axis=0)

                if dubr is not None:
                    d = read_pad(dubr, dch, n) * dub_gain
                    if lev_seg is not None:
                        d = d * lev_seg[:len(d), None]
                    if ch == 6:
                        if dch == 6:
                            core += d
                        else:
                            core[:, 2] += d[:, 0]            # mono dublyaj -> markaz kanal (FC)
                    elif ch == 2:
                        core += d if dch == 2 else d[:, [0, 0]]
                    else:
                        core[:, 0] += d[:, 0]

                peak = max(peak, float(np.max(np.abs(core))) if n else 0.0)
                core, nc = soft_limit(core)
                clipped += nc
                try:
                    writer.p.stdin.write(core.astype("<f4").tobytes())
                except (BrokenPipeError, OSError):
                    self._chk()                          # Stop bosilgan bo'lsa - bu xato emas
                    raise RuntimeError("Kodlashda xatolik (FFmpeg):\n" + writer.tail())

                pos += n
                frac = pos / (total * SR) if total else None
                el = time.time() - tstart
                if frac:
                    frac_c = min(frac, 1.0)
                    eta = el / frac_c * (1 - frac_c)
                    speed = (pos / SR) / max(el, 1e-6)
                    self._prog(w_ai + w_duck, w_main, frac_c,
                               f"{fmt_time(pos / SR)} / {fmt_time(total)}   |   tezlik {speed:.1f}x   |   "
                               f"qoldi ~ {fmt_time(eta)}")
                else:
                    self.progress(None, f"{fmt_time(pos / SR)} qayta ishlandi")

                prev = np.concatenate([prev, cur])[-CTX:]
                for ax_ in (dax, aix, fcx, rrx):
                    if ax_:
                        ax_.advance()
                if len(nxt) == 0:
                    break
                cur = nxt

            rc = writer.finish()
            if rc != 0:
                raise RuntimeError("Kodlash xatosi (FFmpeg):\n" + writer.tail())
            main.kill()
            self._chk()
            out_tmp = None
            ok = True
            self.progress(1.0, "Tayyor")
            took = time.time() - self.t0
            if e_in.sum() > 0:
                names = {6: ["FL", "FR", "FC", "LFE", "SL", "SR"], 2: ["L", "R"], 1: ["M"]}[ch]
                parts, weak = [], []
                for i, nm in enumerate(names):
                    if e_in[i] < 1e-9:
                        continue
                    red = 10 * math.log10((e_in[i] + 1e-12) / (e_out[i] + 1e-12))
                    parts.append(f"{nm} -{max(red, 0):.0f}")
                    if red < 3 and nm != "LFE":
                        weak.append(nm)
                self.log("Dublyaj joylarida original pasayishi (dB): " + ", ".join(parts))
                if weak:
                    self.log("DIQQAT: " + ", ".join(weak) + " kanalda original deyarli pasaymagan. 'Original masofasi' ni "
                             "oshiring yoki 'Maksimal pasayish' ni ko'taring.")
            self.log(f"Eng baland cho'qqi: {20 * math.log10(max(peak, 1e-9)):.1f} dBFS"
                     + (f"  (limiter {clipped} namunaga ta'sir qildi)" if clipped else ""))
            self.log(f"TAYYOR: {st.dst}")
            self.log(f"Sarflangan vaqt: {fmt_time(took)}")
            msg = st.dst

        except Cancelled:
            msg = "To'xtatildi."
            self.log("To'xtatildi (Stop bosildi).")
        except Exception as e:                          # noqa
            msg = str(e)
            self.log("XATO: " + msg)
        finally:
            for p in self.procs:
                if isinstance(p, FF):
                    p.kill()
                else:
                    try:
                        p.kill()
                    except Exception:
                        pass
            if self.tmp and os.path.isdir(self.tmp):
                shutil.rmtree(self.tmp, ignore_errors=True)
            if out_tmp and os.path.exists(out_tmp):
                try:
                    time.sleep(0.3)
                    os.remove(out_tmp)
                    self.log("Chala qolgan chiqish fayli o'chirildi.")
                except OSError:
                    pass
        return ok, msg



# ----------------------------------------------------------------------------------------
#  Ko'p fayl (navbat) yordamchilari
# ----------------------------------------------------------------------------------------
def natural_key(p):
    b = os.path.basename(p).lower()
    return [int(t) if t.isdigit() else t for t in re.split(r"(\d+)", b)]


_NOT_EP = {264, 265, 1080, 720, 480, 2160, 576, 1920, 1280, 4096}


def episode_no(path):
    """Fayl nomidan qism raqamini topadi: S01E05 -> 5, 'Vision Quest 1-5.wav' -> 5, 'Gnomes 06' -> 6."""
    stem = os.path.splitext(os.path.basename(path))[0]
    m = re.search(r"[Ss]\d+\s*[._-]?\s*[Ee](\d+)", stem)
    if m:
        return int(m.group(1))
    m = re.search(r"(?<![A-Za-z0-9])(?:ep|episode|qism|seriya|серия)\s*[._-]?\s*(\d+)", stem, re.I)
    if m:
        return int(m.group(1))
    nums = [int(x) for x in re.findall(r"\d+", stem) if int(x) not in _NOT_EP]
    return nums[-1] if nums else None


def auto_pair(origs, dubs):
    """Original va dublyaj fayllarni juftlaydi: avval qism raqami bo'yicha, bo'lmasa tartib bo'yicha."""
    origs = sorted(origs, key=natural_key)
    dubs = sorted(dubs, key=natural_key)
    eo = [episode_no(x) for x in origs]
    ed = [episode_no(x) for x in dubs]
    ok = (origs and dubs and None not in eo and None not in ed
          and len(set(eo)) == len(eo) and len(set(ed)) == len(ed))
    if ok:
        dmap = dict(zip(ed, dubs))
        pairs = [(o, dmap.get(e, "")) for o, e in zip(origs, eo)]
        used = set(x for _, x in pairs if x)
        rest = [d for d in dubs if d not in used]
        for d in rest:                                  # originalsiz dublyaj
            pairs.append(("", d))
        return pairs, "qism raqami bo'yicha"
    n = max(len(origs), len(dubs))
    pairs = [(origs[i] if i < len(origs) else "", dubs[i] if i < len(dubs) else "") for i in range(n)]
    return pairs, "tartib bo'yicha"


# ----------------------------------------------------------------------------------------
#  GUI
# ----------------------------------------------------------------------------------------
# ----------------------------------------------------------------------------------------
#  UI KIT: logotip va ikonkalar (rasm fayllarsiz — kod bilan chiziladi, silliq/antialias)
# ----------------------------------------------------------------------------------------
import base64 as _b64
import struct as _struct
import zlib as _zlib

_ICON_CACHE = {}


def _png_bytes(rgba):
    h, w, _ = rgba.shape
    raw = b"".join(b"\x00" + rgba[y].tobytes() for y in range(h))

    def chunk(t, d):
        c = _struct.pack(">I", len(d)) + t + d
        return c + _struct.pack(">I", _zlib.crc32(t + d) & 0xFFFFFFFF)
    return (b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", _struct.pack(">IIBBBBB", w, h, 8, 6, 0, 0, 0))
            + chunk(b"IDAT", _zlib.compress(raw, 6)) + chunk(b"IEND", b""))


def _hex(c):
    c = c.lstrip("#")
    return tuple(int(c[i:i + 2], 16) for i in (0, 2, 4))


def _cover(prims, N):
    """Primitivlar to'plamining N x N maskasi (0..1 koordinatalarda)."""
    ys, xs = np.mgrid[0:N, 0:N]
    xs = (xs + 0.5) / N
    ys = (ys + 0.5) / N
    m = np.zeros((N, N), bool)
    for p in prims:
        if p[0].startswith("-"):                 # "-rrect" va h.k.: shakldan teshik ochadi
            m &= ~_cover([(p[0][1:],) + tuple(p[1:])], N)
            continue
        k = p[0]
        if k == "cap":                       # chiziq (yumaloq uchlari bilan)
            _, x1, y1, x2, y2, r = p
            dx, dy = x2 - x1, y2 - y1
            L2 = dx * dx + dy * dy or 1e-9
            t = np.clip(((xs - x1) * dx + (ys - y1) * dy) / L2, 0, 1)
            m |= (xs - (x1 + t * dx)) ** 2 + (ys - (y1 + t * dy)) ** 2 <= r * r
        elif k == "circ":
            _, cx, cy, r = p
            m |= (xs - cx) ** 2 + (ys - cy) ** 2 <= r * r
        elif k == "ring":
            _, cx, cy, r, w = p
            d = np.sqrt((xs - cx) ** 2 + (ys - cy) ** 2)
            m |= np.abs(d - r) <= w / 2
        elif k == "rrect":
            _, x, y, w, h, rad = p
            qx = np.abs(xs - (x + w / 2)) - (w / 2 - rad)
            qy = np.abs(ys - (y + h / 2)) - (h / 2 - rad)
            d = np.sqrt(np.maximum(qx, 0) ** 2 + np.maximum(qy, 0) ** 2) + np.minimum(np.maximum(qx, qy), 0) - rad
            m |= d <= 0
        elif k == "tri":
            _, x1, y1, x2, y2, x3, y3 = p
            def s(ax, ay, bx, by):
                return (xs - bx) * (ay - by) - (ax - bx) * (ys - by)
            d1, d2, d3 = s(x1, y1, x2, y2), s(x2, y2, x3, y3), s(x3, y3, x1, y1)
            neg = (d1 < 0) | (d2 < 0) | (d3 < 0)
            pos = (d1 > 0) | (d2 > 0) | (d3 > 0)
            m |= ~(neg & pos)
    return m


def _down(m, size, ss):
    return m.reshape(size, ss, size, ss).mean(axis=(1, 3))


ICONS = {
    "play": [("tri", .28, .16, .28, .84, .84, .5)],
    "stop": [("rrect", .22, .22, .56, .56, .08)],
    "plus": [("cap", .5, .2, .5, .8, .07), ("cap", .2, .5, .8, .5, .07)],
    "trash": [("rrect", .27, .32, .46, .52, .06), ("cap", .2, .27, .8, .27, .05), ("cap", .4, .17, .6, .17, .05)],
    "up": [("cap", .5, .25, .22, .58, .06), ("cap", .5, .25, .78, .58, .06), ("cap", .5, .25, .5, .8, .06)],
    "down": [("cap", .5, .75, .22, .42, .06), ("cap", .5, .75, .78, .42, .06), ("cap", .5, .75, .5, .2, .06)],
    "folder": [("rrect", .12, .3, .76, .5, .08), ("rrect", .12, .2, .34, .24, .06)],
    "file": [("rrect", .24, .12, .52, .76, .07), ("-cap", .36, .38, .64, .38, .035), ("-cap", .36, .52, .64, .52, .035), ("-cap", .36, .66, .54, .66, .035)],
    "download": [("cap", .5, .12, .5, .6, .075), ("cap", .5, .64, .25, .4, .075), ("cap", .5, .64, .75, .4, .075),
                 ("cap", .18, .84, .82, .84, .075), ("cap", .18, .84, .18, .68, .075), ("cap", .82, .84, .82, .68, .075)],
    "link": [("ring", .35, .65, .17, .1), ("ring", .65, .35, .17, .1), ("cap", .42, .58, .58, .42, .06)],
    "film": [("rrect", .14, .16, .72, .68, .07)] + [("-rrect", .2, .24 + i * .2, .09, .1, .02) for i in range(3)]
            + [("-rrect", .71, .24 + i * .2, .09, .1, .02) for i in range(3)] + [("-rrect", .36, .3, .28, .4, .03)],
    "merge": [("rrect", .1, .3, .34, .4, .06), ("rrect", .56, .3, .34, .4, .06), ("cap", .43, .5, .57, .5, .05)],
    "queue": [("cap", .22, .3, .78, .3, .06), ("cap", .22, .5, .78, .5, .06), ("cap", .22, .7, .6, .7, .06)],
    "gear": [("ring", .5, .5, .24, .13)] + [("cap", .5 + .3 * math.cos(a * math.pi / 4), .5 + .3 * math.sin(a * math.pi / 4),
                                            .5 + .4 * math.cos(a * math.pi / 4), .5 + .4 * math.sin(a * math.pi / 4), .07) for a in range(8)],
    "wave": [("cap", .2, .38, .2, .62, .06), ("cap", .35, .22, .35, .78, .06), ("cap", .5, .12, .5, .88, .06),
             ("cap", .65, .28, .65, .72, .06), ("cap", .8, .4, .8, .6, .06)],
    "check": [("cap", .22, .52, .43, .72, .07), ("cap", .43, .72, .8, .3, .07)],
    "info": [("ring", .5, .5, .36, .08), ("cap", .5, .45, .5, .7, .06), ("circ", .5, .3, .06)],
    "refresh": [("ring", .5, .52, .3, .09), ("-rrect", .55, .1, .45, .3, 0), ("tri", .58, .1, .58, .46, .9, .28)],
    "skip": [("tri", .2, .2, .2, .8, .55, .5), ("cap", .75, .2, .75, .8, .07)],
}


def icon_image(name, size=20, color="#e8e8ec", master=None):
    """tk.PhotoImage (silliq antialias) — kalit bo'yicha keshlanadi."""
    import tkinter as tk
    key = (name, size, color)
    if key in _ICON_CACHE:
        return _ICON_CACHE[key]
    ss = 4
    N = size * ss
    a = _down(_cover(ICONS[name], N), size, ss)
    r, g, b = _hex(color)
    rgba = np.zeros((size, size, 4), np.uint8)
    rgba[..., 0], rgba[..., 1], rgba[..., 2] = r, g, b
    rgba[..., 3] = np.clip(a * 255, 0, 255).astype(np.uint8)
    img = tk.PhotoImage(master=master, data=_b64.b64encode(_png_bytes(rgba)))
    _ICON_CACHE[key] = img
    return img


def logo_rgba(size=64):
    """Ilova logotipi: gradientli yumaloq kvadrat + ovoz to'lqini + dublyaj (mikrofon nuqtasi)."""
    ss = 4 if size <= 128 else 2
    N = size * ss
    ys, xs = np.mgrid[0:N, 0:N]
    u, v = (xs + .5) / N, (ys + .5) / N
    base = _cover([("rrect", .03, .03, .94, .94, .22)], N)
    c1, c2 = np.array(_hex("#3b82f6"), float), np.array(_hex("#8b5cf6"), float)
    t = np.clip((u * .55 + v * .75), 0, 1)[..., None]
    col = c1 * (1 - t) + c2 * t
    gloss = np.clip(1 - v * 1.6, 0, 1)[..., None] * 38
    col = np.clip(col + gloss, 0, 255)
    bars = [(.2, .36, .64), (.32, .24, .76), (.44, .14, .86), (.56, .3, .7), (.68, .22, .78), (.8, .38, .62)]
    wm = _cover([("cap", x, y1, x, y2, .042) for x, y1, y2 in bars], N)
    out = np.zeros((N, N, 4), float)
    out[..., :3] = col
    out[..., 3] = base * 255
    w = wm[..., None] & base[..., None]
    out[..., :3] = np.where(w, 255, out[..., :3])
    sm = _cover([("circ", .8, .2, .07)], N)[..., None]
    out[..., :3] = np.where(sm, np.array(_hex("#34d399"), float), out[..., :3])
    px = out.reshape(size, ss, size, ss, 4)
    a = px[..., 3].mean(axis=(1, 3))
    rgb = (px[..., :3] * px[..., 3:4]).sum(axis=(1, 3)) / np.maximum(px[..., 3:4].sum(axis=(1, 3)), 1e-6)
    res = np.zeros((size, size, 4), np.uint8)
    res[..., :3] = np.clip(rgb, 0, 255).astype(np.uint8)
    res[..., 3] = np.clip(a, 0, 255).astype(np.uint8)
    return res


def logo_image(size=64, master=None):
    import tkinter as tk
    key = ("logo", size)
    if key not in _ICON_CACHE:
        _ICON_CACHE[key] = tk.PhotoImage(master=master, data=_b64.b64encode(_png_bytes(logo_rgba(size))))
    return _ICON_CACHE[key]


def save_ico(path):
    """Windows .ico (PNG ichida) — ярлык / EXE uchun."""
    sizes = (16, 32, 48, 64, 128, 256)
    pngs = [_png_bytes(logo_rgba(s)) for s in sizes]
    head = _struct.pack("<HHH", 0, 1, len(sizes))
    off = 6 + 16 * len(sizes)
    ent = b""
    for s, p in zip(sizes, pngs):
        ent += _struct.pack("<BBBBHHII", s % 256, s % 256, 0, 0, 1, 32, len(p), off)
        off += len(p)
    with open(path, "wb") as f:
        f.write(head + ent + b"".join(pngs))


# ----------------------------------------------------------------------------------------
#  INTRO QO'SHUVCHI (kino boshiga reklama) — dastur ichidagi alohida oyna
# ----------------------------------------------------------------------------------------
NO_WINDOW = getattr(subprocess, "CREATE_NO_WINDOW", 0)
VIDEO_TYPES = [("Video fayllar", "*.mp4 *.mkv *.avi *.mov *.m4v *.ts *.webm *.flv"),
               ("Barcha fayllar", "*.*")]

ENC_STATS = re.compile(r"^(encoded \d+ frames|x26[45] \[|\[libx26[45]|\[x26[45])")
PROGRESS_KEYS = re.compile(
    r"^(frame|fps|stream_\d+_\d+_q|bitrate|total_size|out_time_us|out_time_ms|"
    r"out_time|dup_frames|drop_frames|speed|progress)=")

VIDEO_ENC = {
    "h264": "libx264", "hevc": "libx265", "vp9": "libvpx-vp9",
    "vp8": "libvpx", "av1": "libsvtav1", "mpeg4": "mpeg4",
    "mpeg2video": "mpeg2video",
}
AUDIO_ENC = {
    "aac": "aac", "ac3": "ac3", "eac3": "eac3", "mp3": "libmp3lame",
    "opus": "libopus", "vorbis": "libvorbis", "flac": "flac", "mp2": "mp2",
    "pcm_s16le": "pcm_s16le", "dts": "dca", "truehd": "truehd",
}
LOSSY_AUDIO = {"aac", "ac3", "eac3", "mp3", "opus", "vorbis", "mp2", "dts"}

MP4_EXTS = (".mp4", ".m4v", ".mov")
MP4_VIDEO_OK = {"h264", "hevc", "av1", "vp9", "mpeg4", "mpeg2video", "mjpeg"}
MP4_AUDIO_OK = {"aac", "ac3", "eac3", "mp3", "mp2", "opus", "flac", "alac"}
WEBM_VIDEO_OK = {"vp8", "vp9", "av1"}
WEBM_AUDIO_OK = {"opus", "vorbis"}

TEXT_SUBS = {"subrip", "srt", "ass", "ssa", "webvtt", "mov_text", "text", "subviewer",
             "subviewer1", "microdvd", "mpl2", "jacosub", "realtext", "sami", "stl",
             "vplayer", "pjs"}
BITMAP_SUBS_MKV = {"hdmv_pgs_subtitle", "dvd_subtitle", "dvb_subtitle"}

# Vaqt belgilari bilan bog'liq ffmpeg ogohlantirishlari (sanash uchun)
TS_WARN = ("Non-monotonic", "Past duration", "Application provided invalid",
           "Timestamps are unset", "timestamp discontinuity")


class IJCancelled(Exception):
    pass


# --------------------------------------------------------------------------
# Yordamchi funksiyalar
# --------------------------------------------------------------------------
def _float(x, default=0.0):
    try:
        return float(x)
    except (TypeError, ValueError):
        return default


def stream_duration(st):
    d = _float(st.get("duration"))
    if d > 0:
        return d
    t = get_tag(st, "DURATION")           # MKV: "00:42:10.123000000"
    if t:
        try:
            h, m, sec = str(t).split(":")
            return int(h) * 3600 + int(m) * 60 + float(sec)
        except ValueError:
            pass
    return 0.0


def ij_probe(ffprobe, path):
    r = subprocess.run(
        [ffprobe, "-v", "error", "-print_format", "json",
         "-show_streams", "-show_format", "-show_chapters", path],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        creationflags=NO_WINDOW)
    if r.returncode != 0:
        raise RuntimeError("ffprobe xatosi (%s): %s" % (os.path.basename(path), r.stderr.strip()))
    d = json.loads(r.stdout)
    streams = d.get("streams", [])
    fmt = d.get("format", {}) or {}
    vids = [s for s in streams if s.get("codec_type") == "video"
            and not s.get("disposition", {}).get("attached_pic")]
    if not vids:
        raise RuntimeError("Video oqim topilmadi: " + os.path.basename(path))
    extra = {}
    r2 = subprocess.run(      # extradata (AAC ASC va h.k.) faqat audio oqimlar uchun
        [ffprobe, "-v", "error", "-print_format", "json", "-select_streams", "a",
         "-show_streams", "-show_data", path],
        capture_output=True, text=True, encoding="utf-8", errors="replace", creationflags=NO_WINDOW)
    if r2.returncode == 0:
        try:
            extra = {x.get("index"): x.get("extradata") for x in json.loads(r2.stdout).get("streams", [])}
        except ValueError:
            extra = {}
    r3 = subprocess.run(      # video (SPS/PPS/VPS) extradata
        [ffprobe, "-v", "error", "-print_format", "json", "-select_streams", "v:0",
         "-show_streams", "-show_data", path],
        capture_output=True, text=True, encoding="utf-8", errors="replace", creationflags=NO_WINDOW)
    if r3.returncode == 0:
        try:
            for x in json.loads(r3.stdout).get("streams", []):
                extra[x.get("index")] = x.get("extradata")
        except ValueError:
            pass
    for st in streams:
        st["_extra"] = hex_extradata(extra.get(st.get("index")))
    auds = [s for s in streams if s.get("codec_type") == "audio"]
    subs = [s for s in streams if s.get("codec_type") == "subtitle"]
    # davomiylik: video/audio oqimlari bo'yicha (subtitr oxirgi qatori kinodan uzoqroq bo'lishi mumkin)
    sdur = [stream_duration(x) for x in vids[:1] + auds if stream_duration(x) > 0]
    dur = max(sdur) if sdur else (_float(fmt.get("duration")) or _float(vids[0].get("duration")))
    try:
        fbr = int(fmt.get("bit_rate") or 0)
    except ValueError:
        fbr = 0
    return {"video": vids[0], "audio": auds, "subs": subs, "duration": dur, "bitrate": fbr,
            "format_name": fmt.get("format_name", "") or "",
            "tags": fmt.get("tags", {}) or {},
            "chapters": d.get("chapters", []) or [],
            "attach": [x for x in streams if x.get("codec_type") == "attachment"]}


def hex_extradata(text):
    """ffprobe -show_data hex dump ("00000000: 1190 56e5 00  ..V..") ni baytlarga aylantiradi."""
    out = bytearray()
    for line in (text or "").splitlines():
        m = re.match(r"\s*[0-9a-fA-F]{8}:\s((?:[0-9a-fA-F]{2,4} ?)+)", line)
        if m:
            out += bytes.fromhex(m.group(1).replace(" ", ""))
    return bytes(out)


SELF_DESCRIBING = {"mp3", "mp2", "ac3", "eac3", "dts", "truehd"}
AAC_SF = [96000, 88200, 64000, 48000, 44100, 32000, 24000, 22050, 16000, 12000, 11025, 8000, 7350]


class _Bits:
    def __init__(self, data):
        self.d, self.pos = data, 0

    def left(self):
        return len(self.d) * 8 - self.pos

    def read(self, n):
        v = 0
        for _ in range(n):
            if self.pos >= len(self.d) * 8:
                raise ValueError("ASC tugadi")
            v = (v << 1) | ((self.d[self.pos >> 3] >> (7 - (self.pos & 7))) & 1)
            self.pos += 1
        return v


def parse_asc(data):
    """AAC AudioSpecificConfig ning MA'NOSINI qaytaradi (bayt-bayt emas): LC/HE/HEv2, sample rate, kanallar, SBR/PS."""
    if not data:
        return None
    try:
        r = _Bits(data)

        def aot():
            t = r.read(5)
            return 32 + r.read(6) if t == 31 else t

        def sfreq():
            i = r.read(4)
            return r.read(24) if i == 15 else AAC_SF[i]

        t = aot()
        sf = sfreq()
        ch = r.read(4)
        sbr = ps = False
        if t in (5, 29):                 # aniq (explicit) HE-AAC belgisi
            sbr, ps = True, t == 29
            sfreq()
            t = aot()
        flen = r.read(1)
        if r.read(1):
            r.read(14)
        r.read(1)
        # orqaga mos (backward compatible) SBR/PS belgilari
        while r.left() >= 16:
            sync = r.read(11)
            if sync == 0x2b7:
                if aot() == 5:
                    sbr = bool(r.read(1))
                    if sbr:
                        sfreq()
                        if r.left() >= 12 and r.read(11) == 0x548:
                            ps = bool(r.read(1))
            elif sync == 0x548:
                ps = bool(r.read(1))
            break
        return (t, sf, ch, flen, sbr, ps)
    except (ValueError, IndexError):
        return None


def xiph_headers(extra):
    """Vorbis extradata (Xiph lacing) dan identifikatsiya va setup (kodlar jadvali) sarlavhalarini ajratadi."""
    try:
        if not extra or extra[0] != 2:
            return None
        i, sizes = 1, []
        for _ in range(2):
            n = 0
            while True:
                b = extra[i]
                i += 1
                n += b
                if b != 255:
                    break
            sizes.append(n)
        h1 = extra[i:i + sizes[0]]
        h3 = extra[i + sizes[0] + sizes[1]:]
        if len(h1) >= 30:
            h1 = h1[:16] + h1[28:]       # bitreyt maydonlari (max/nominal/min) dekodlashga ta'sir qilmaydi
        return h1, h3
    except IndexError:
        return None


def audio_params_match(a, b):
    """Ikki audio oqim bitta trekka joylanganda bir xil dekodlanadimi (extradata ma'nosi bo'yicha, bayt-bayt emas)."""
    ea, eb = a.get("_extra") or b"", b.get("_extra") or b""
    ca, cb = a.get("codec_name"), b.get("codec_name")
    if ca != cb:
        return False
    if ca == "aac":
        pa, pb = parse_asc(ea), parse_asc(eb)
        if pa is not None and pb is not None:
            return pa == pb
    elif ca == "vorbis":
        ha, hb = xiph_headers(ea), xiph_headers(eb)
        if ha is not None and hb is not None:
            return ha == hb          # komment sarlavhasi hisobga olinmaydi
    elif ca == "opus":
        if ea[:8] == b"OpusHead" and eb[:8] == b"OpusHead" and len(ea) >= 19 and len(eb) >= 19:
            return ea[9:10] == eb[9:10] and ea[18:] == eb[18:]   # kanallar va mapping (pre-skip/gain hisobga olinmaydi)
    elif ca == "flac":
        key = lambda x: (str(x.get("sample_rate")), str(x.get("channels")), str(x.get("bits_per_raw_sample")))
        return key(a) == key(b)
    elif ca in SELF_DESCRIBING or (ca or "").startswith("pcm_"):
        # har bir kadr o'z sarlavhasiga ega: konteynerdagi extradata (masalan AVI ning WAVEFORMATEX qo'shimchasi) ahamiyatsiz
        return (str(a.get("sample_rate")) == str(b.get("sample_rate"))
                and int(a.get("channels", 0) or 0) == int(b.get("channels", 0) or 0))
    return ea == eb


def audio_label(a):
    prof = a.get("profile")
    return "%s%s" % (a.get("codec_name"), " " + prof if prof and prof != "unknown" else "")


def audio_plan(ffmpeg, movie):
    """Har bir kino audio treki uchun reklama kodlovchisi; None — mos kodlovchi yo'q (dummy)."""
    plan = []
    for a in movie["audio"]:
        c = a.get("codec_name")
        enc = AUDIO_ENC.get(c)
        if enc and c == "aac" and "HE" in (a.get("profile") or "").upper():
            enc = "libfdk_aac"      # HE-AAC ni faqat fdk kodlay oladi
        if not enc or not encoder_available(ffmpeg, enc):
            enc = None
        plan.append(enc)
    return plan


def _pcm_stats(ffmpeg, path, track, start, seconds):
    """Audio trekdan `seconds` soniya dekodlab (mono, 16 kHz), (RMS, nol kesishishlar ulushi) ni qaytaradi."""
    import array
    r = subprocess.run(
        [ffmpeg, "-v", "error", "-nostdin", "-ss", "%.3f" % start, "-t", "%.3f" % seconds, "-i", path,
         "-map", "0:a:%d" % track, "-ac", "1", "-ar", "16000", "-f", "s16le", "-"],
        capture_output=True, creationflags=NO_WINDOW)
    if r.returncode != 0 or len(r.stdout) < 2000:
        return None
    a = array.array("h")
    a.frombytes(r.stdout[: len(r.stdout) // 2 * 2])
    n = len(a)
    rms = (sum(x * x for x in a) / n) ** 0.5
    zc = sum(1 for i in range(1, n) if (a[i - 1] < 0) != (a[i] < 0)) / n
    return rms, zc


def audio_sanity(ffmpeg, final_path, movie_path, offset, movie_dur, n_tracks):
    """Har bir audio trek uchun: tayyor fayldagi kino qismi asl kino bilan bir xil eshitiladimi
    (kuchi va chastotasi bo'yicha). Buzilgan yoki ovozsiz treklar ro'yxatini qaytaradi."""
    bad = []
    t = max(1.0, min(60.0, movie_dur * 0.3))
    span = min(6.0, max(2.0, movie_dur * 0.1))
    for i in range(n_tracks):
        ref = _pcm_stats(ffmpeg, movie_path, i, t, span)
        got = _pcm_stats(ffmpeg, final_path, i, offset + t, span)
        if ref is None:
            continue                              # kinoning o'zida shu joyda ovoz yo'q — tekshirib bo'lmaydi
        if got is None:
            bad.append((i, "ovoz topilmadi"))
            continue
        (r1, z1), (r2, z2) = ref, got
        if r1 > 50 and (r2 < 0.5 * r1 or r2 > 2.0 * r1):
            bad.append((i, "balandligi farq qiladi (%.0f va %.0f)" % (r2, r1)))
        elif z1 > 0 and abs(z2 - z1) > 0.25 * z1 + 0.01:
            bad.append((i, "tovush tarkibi farq qiladi"))
    return bad


def media_span(ffprobe, path, fallback):
    """Fayldagi barcha video/audio paketlarning haqiqiy uzunligi: eng oxirgi paket oxiri - eng birinchi paket boshi.
    Kino aynan shu vaqtdan boshlanadi, shunda hech bir oqimda ustma-ust tushish yoki bo'shliq qolmaydi."""
    r = subprocess.run(
        [ffprobe, "-v", "error", "-print_format", "json", "-show_entries",
         "packet=stream_index,pts_time,dts_time,duration_time", path],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        creationflags=NO_WINDOW)
    if r.returncode != 0:
        return fallback
    first, last = None, None
    try:
        packets = json.loads(r.stdout).get("packets", [])
    except ValueError:
        return fallback
    for pk in packets:
        t = pk.get("pts_time")
        if t in (None, "N/A"):
            t = pk.get("dts_time")
        try:
            t = float(t)
        except (TypeError, ValueError):
            continue
        d = _float(pk.get("duration_time"))
        first = t if first is None else min(first, t)
        last = t + d if last is None else max(last, t + d)
    if first is None or last is None or last <= first:
        return fallback
    return last - first


STAT_TAGS = re.compile(r"^(BPS|DURATION|NUMBER_OF_BYTES|NUMBER_OF_FRAMES|_STATISTICS_.*)(-.+)?$", re.I)
DISP_KEYS = ("default", "dub", "original", "comment", "lyrics", "karaoke", "forced",
             "hearing_impaired", "visual_impaired", "clean_effects")


def copy_tags(obj):
    """Oqim/konteyner teglari (til, nom...) — eskirib qoladigan MKV statistika teglarisiz."""
    return [(k, v) for k, v in ((obj or {}).get("tags", obj) or {}).items()
            if not STAT_TAGS.match(k) and k.lower() != "encoder"]


def disp_arg(st):
    d = st.get("disposition", {}) or {}
    flags = [k for k in DISP_KEYS if d.get(k)]
    return "+".join(flags) if flags else "0"


def real_container_ext(movie, cur_ext):
    """Kinoning HAQIQIY konteyneriga mos kengaytma (fayl nomidagi kengaytmaga emas, ffprobe ga qarab)."""
    n = movie.get("format_name", "")
    if "matroska" in n or "webm" in n:
        return ".mkv"
    if "mov" in n or "mp4" in n:
        return cur_ext if cur_ext in MP4_EXTS else ".mp4"
    if "mpegts" in n:
        return ".ts"
    return None


def resolve_out_path(ffprobe, movie_path, out):
    """Natija kinoning haqiqiy konteynerida saqlanishi uchun fayl kengaytmasini to'g'rilaydi."""
    try:
        r = subprocess.run([ffprobe, "-v", "error", "-show_entries", "format=format_name", "-of", "csv=p=0",
                            movie_path], capture_output=True, text=True, encoding="utf-8", errors="replace",
                           creationflags=NO_WINDOW)
        ext = os.path.splitext(out)[1].lower()
        rext = real_container_ext({"format_name": r.stdout.strip()}, ext)
        if r.returncode == 0 and rext and rext != ext:
            return os.path.splitext(out)[0] + rext
    except OSError:
        pass
    return out


def ffmetadata_chapters(chapters, offset):
    """Boblar ffmetadata ko'rinishida, reklama uzunligiga siljitilgan holda."""
    def esc(t):
        return re.sub(r"([=;#\\\n])", r"\\\1", t)
    out = [";FFMETADATA1"]
    for c in chapters:
        st, en = _float(c.get("start_time")), _float(c.get("end_time"))
        out += ["[CHAPTER]", "TIMEBASE=1/1000", "START=%d" % round((st + offset) * 1000),
                "END=%d" % round((en + offset) * 1000)]
        title = (c.get("tags") or {}).get("title")
        if title:
            out.append("title=" + esc(title))
    return "\n".join(out) + "\n"


def negative_lead(ffprobe, path):
    """B-kadrli videoda DTS manfiy boshlanadi; muxer (make_zero) hamma narsani shuncha oldinga suradi.
    Boblar ham shunga mos surilishi uchun shu miqdor kerak (soniya)."""
    r = subprocess.run(
        [ffprobe, "-v", "error", "-print_format", "json", "-show_entries", "packet=dts_time,pts_time", path],
        capture_output=True, text=True, encoding="utf-8", errors="replace", creationflags=NO_WINDOW)
    low = 0.0
    try:
        for pk in json.loads(r.stdout).get("packets", []):
            t = _float(pk.get("dts_time") if pk.get("dts_time") not in (None, "N/A") else pk.get("pts_time"), 0.0)
            low = min(low, t)
    except ValueError:
        return 0.0
    return -low


def get_tag(stream_or_fmt_tags, key):
    tags = stream_or_fmt_tags.get("tags", stream_or_fmt_tags) if stream_or_fmt_tags else {}
    for k, v in (tags or {}).items():
        if k.lower() == key.lower():
            return v
    return None


def get_fps(v):
    for key in ("r_frame_rate", "avg_frame_rate"):
        try:
            f = Fraction(v.get(key, "0/1"))
            if f > 0:
                return f
        except (ValueError, ZeroDivisionError):
            pass
    return Fraction(25, 1)


def get_sar(v):
    s = v.get("sample_aspect_ratio", "1:1")
    if not s or s in ("N/A", "0:1", "0:0"):
        return "1:1"
    return s


def describe(info):
    v = info["video"]
    s = "video: %s %s %dx%d %s %.3ffps  [%s]" % (
        v.get("codec_name"), v.get("profile", ""), v.get("width", 0), v.get("height", 0),
        v.get("pix_fmt"), float(get_fps(v)), info.get("format_name", "?"))
    for i, a in enumerate(info["audio"]):
        try:
            kbps = " %d kbit/s" % (int(a.get("bit_rate") or 0) // 1000) if a.get("bit_rate") else ""
        except ValueError:
            kbps = ""
        s += "\n    audio#%d: %s %sHz %dch%s" % (
            i, audio_label(a), a.get("sample_rate"), int(a.get("channels", 0) or 0), kbps)
    if not info["audio"]:
        s += "\n    audio: yo'q"
    if info["subs"]:
        kinds = {}
        for x in info["subs"]:
            kinds[x.get("codec_name", "?")] = kinds.get(x.get("codec_name", "?"), 0) + 1
        s += "\n    subtitr: %d ta (%s)" % (
            len(info["subs"]), ", ".join("%s x%d" % kv for kv in kinds.items()))
    return s


def short_desc(info):
    """Bitta qatorli qisqa tavsif (oddiy log uchun)."""
    v = info["video"]
    pf = v.get("pix_fmt") or ""
    depth = " 10-bit" if "10" in pf else (" 12-bit" if "12" in pf else "")
    hdr = {"pq": " HDR10", "hlg": " HLG"}.get(hdr_kind(v), "")
    parts = ["%s%s%s %dx%d %.3gfps" % ((v.get("codec_name") or "?").upper(), depth, hdr,
                                      int(v.get("width", 0)), int(v.get("height", 0)), float(get_fps(v)))]
    if info["audio"]:
        parts.append(", ".join("%s %dch %.3gkHz" % (audio_label(a), int(a.get("channels", 0) or 0),
                                                    float(a.get("sample_rate") or 0) / 1000) for a in info["audio"]))
    else:
        parts.append("audio yo'q")
    if info["subs"]:
        parts.append("subtitr: %d" % len(info["subs"]))
    return " | ".join(parts)


def compare(movie, intro):
    """Mos kelmaslik sabablari ro'yxatini qaytaradi (bo'sh bo'lsa — mos)."""
    why = []
    mv, iv = movie["video"], intro["video"]
    if mv.get("codec_name") != iv.get("codec_name"):
        why.append("video kodek: %s != %s" % (mv.get("codec_name"), iv.get("codec_name")))
    if mv.get("profile") and iv.get("profile") and mv["profile"] != iv["profile"]:
        why.append("video profil: %s != %s" % (mv["profile"], iv["profile"]))
    if mv.get("pix_fmt") != iv.get("pix_fmt"):
        why.append("pixel format: %s != %s" % (mv.get("pix_fmt"), iv.get("pix_fmt")))
    if (mv.get("width"), mv.get("height")) != (iv.get("width"), iv.get("height")):
        why.append("o'lcham: %sx%s != %sx%s" % (mv.get("width"), mv.get("height"),
                                                 iv.get("width"), iv.get("height")))
    if abs(float(get_fps(mv)) - float(get_fps(iv))) > 0.01:
        why.append("FPS: %.3f != %.3f" % (float(get_fps(mv)), float(get_fps(iv))))
    if get_sar(mv) != get_sar(iv):
        why.append("SAR: %s != %s" % (get_sar(mv), get_sar(iv)))
    ma, ia = movie["audio"], intro["audio"]
    if len(ma) != len(ia):
        why.append("audio oqimlar soni: %d != %d" % (len(ma), len(ia)))
    else:
        for i, (a, b) in enumerate(zip(ma, ia)):
            if a.get("codec_name") != b.get("codec_name"):
                why.append("audio#%d kodek: %s != %s" % (i, a.get("codec_name"), b.get("codec_name")))
            if str(a.get("sample_rate")) != str(b.get("sample_rate")):
                why.append("audio#%d sample rate: %s != %s" % (i, a.get("sample_rate"), b.get("sample_rate")))
            if int(a.get("channels", 0) or 0) != int(b.get("channels", 0) or 0):
                why.append("audio#%d kanallar: %s != %s" % (i, a.get("channels"), b.get("channels")))
    return why


def timebase_mismatch(movie, other, skip=()):
    """concat demuxer barcha fayllarda bir xil time_base talab qiladi."""
    bad = []
    if movie["video"].get("time_base") != other["video"].get("time_base"):
        bad.append("video: %s != %s" % (movie["video"].get("time_base"), other["video"].get("time_base")))
    if len(movie["audio"]) != len(other["audio"]):
        bad.append("audio oqimlar soni: %d != %d" % (len(movie["audio"]), len(other["audio"])))
    else:
        for i, (a, b) in enumerate(zip(movie["audio"], other["audio"])):
            if i not in skip and a.get("time_base") != b.get("time_base"):
                bad.append("audio#%d: %s != %s" % (i, a.get("time_base"), b.get("time_base")))
    return bad


def intro_container(movie):
    """Reklama kinoning HAQIQIY konteyneri (fayl nomiga emas, ffprobe ga qarab) shaklida yoziladi."""
    n = movie.get("format_name", "")
    if "matroska" in n or "webm" in n:
        return ".mkv"
    if "mov" in n or "mp4" in n:
        return ".mp4"
    if "mpegts" in n:
        return ".ts"
    return ".mkv"  # boshqalar uchun: timebase mos kelmasa, kino MKV ga ko'chiriladi


def mp4_timescale_args(movie):
    try:
        tb = Fraction(movie["video"].get("time_base", "0/1"))
        if tb > 0 and tb.numerator == 1:
            return ["-video_track_timescale", str(tb.denominator)]
    except (ValueError, ZeroDivisionError):
        pass
    return []


def container_problems(info, ext):
    bad = []
    if ext in MP4_EXTS:
        vok, aok = MP4_VIDEO_OK, MP4_AUDIO_OK
    elif ext == ".webm":
        vok, aok = WEBM_VIDEO_OK, WEBM_AUDIO_OK
    else:
        return bad
    vc = info["video"].get("codec_name")
    if vc not in vok:
        bad.append("video %s" % vc)
    for a in info["audio"]:
        if a.get("codec_name") not in aok:
            bad.append("audio %s" % a.get("codec_name"))
    return bad


def plan_subs(subs, ext):
    """Qaysi subtitrlar chiqish konteyneriga qaysi kodek bilan o'tishini belgilaydi."""
    keep, skipped = [], []
    for s in subs:
        c = s.get("codec_name", "")
        codec = None
        if ext in MP4_EXTS:
            if c in TEXT_SUBS:
                codec = "mov_text"
        elif ext in (".mkv", ".mks"):
            if c in ("subrip", "ass", "ssa", "webvtt") or c in BITMAP_SUBS_MKV:
                codec = "copy"
            elif c in TEXT_SUBS:
                codec = "subrip"
        elif ext == ".webm":
            if c in TEXT_SUBS:
                codec = "webvtt"
        if codec == c:
            codec = "copy"
        if codec:
            keep.append((s, codec))
        else:
            skipped.append(c or "?")
    return keep, skipped


# H.264 level chegaralari (Baseline/Main uchun): (MaxBR kbit/s, MaxCPB kbit)
H264_LEVELS = {10: (64, 175), 11: (192, 500), 12: (384, 1000), 13: (768, 2000),
               20: (2000, 2000), 21: (4000, 4000), 22: (4000, 4000),
               30: (10000, 10000), 31: (14000, 14000), 32: (20000, 20000),
               40: (20000, 25000), 41: (50000, 62500), 42: (50000, 62500),
               50: (135000, 135000), 51: (240000, 240000), 52: (240000, 240000)}


def h264_limits(level, profile):
    """Level va profilga ko'ra (maxrate, bufsize) bit/s da; noma'lum bo'lsa None."""
    lim = H264_LEVELS.get(level)
    if not lim:
        return None
    f = {"high": 1.25, "high 10": 3, "high 4:2:2": 4, "high 4:4:4 predictive": 4}.get((profile or "").lower(), 1)
    return int(lim[0] * f * 1000), int(lim[1] * f * 1000)


def h264_profile(p):
    p = (p or "").lower()
    table = {
        "constrained baseline": "baseline", "baseline": "baseline",
        "main": "main", "high": "high", "high 10": "high10",
        "high 4:2:2": "high422", "high 4:4:4 predictive": "high444",
    }
    return table.get(p)


_ENC_CACHE = {}


def encoder_available(ffmpeg, name):
    if ffmpeg not in _ENC_CACHE:
        r = subprocess.run([ffmpeg, "-hide_banner", "-encoders"], capture_output=True,
                           text=True, encoding="utf-8", errors="replace", creationflags=NO_WINDOW)
        _ENC_CACHE[ffmpeg] = r.stdout
    return (" %s " % name) in _ENC_CACHE[ffmpeg]


# ---- HDR (HEVC/AV1 PQ va HLG) -------------------------------------------------
PQ, HLG = "smpte2084", "arib-std-b67"


def hdr_kind(v):
    t = v.get("color_transfer")
    return "pq" if t == PQ else ("hlg" if t == HLG else None)


def _side(v, name):
    for sd in v.get("side_data_list", []) or []:
        if sd.get("side_data_type") == name:
            return sd
    return {}


def _frac(x):
    try:
        return float(Fraction(str(x)))
    except (ValueError, ZeroDivisionError):
        return None


def x265_hdr_params(v):
    """Kino HDR10 bo'lsa: master-display va max-cll ni reklamaga ham yozish uchun x265 parametrlari."""
    out = []
    md = _side(v, "Mastering display metadata")
    keys = ["green_x", "green_y", "blue_x", "blue_y", "red_x", "red_y", "white_point_x", "white_point_y",
            "max_luminance", "min_luminance"]
    vals = [_frac(md.get(k)) for k in keys] if md else []
    if md and all(x is not None for x in vals):
        g = [round(x * 50000) for x in vals[:8]]
        mx, mn = round(vals[8] * 10000), round(vals[9] * 10000)
        out.append("master-display=G(%d,%d)B(%d,%d)R(%d,%d)WP(%d,%d)L(%d,%d)" % (*g, mx, mn))
    cl = _side(v, "Content light level metadata")
    if cl.get("max_content") is not None:
        out.append("max-cll=%d,%d" % (int(cl.get("max_content") or 0), int(cl.get("max_average") or 0)))
    return out


def hdr_filter(movie_v, intro_v, have_zscale):
    """Kino HDR, reklama SDR bo'lsa — reklamani HDR shkalasiga to'g'ri o'tkazadi (oq rang 203 nit).
    Aks holda reklama xira/kulrang ko'rinadi. Qaytaradi: (filtr yoki '', izoh yoki '')."""
    kind = hdr_kind(movie_v)
    if not kind and hdr_kind(intro_v):
        if not have_zscale:
            return "", "ffmpeg'da zscale filtri yo'q: HDR reklama SDR ga o'tkazilmadi"
        return ("zscale=t=linear:npl=1000,format=gbrpf32le,zscale=p=bt709,tonemap=tonemap=hable:desat=0,"
                "zscale=t=bt709:m=bt709:r=tv"), "reklama HDR, kino SDR: reklama SDR ga o'tkaziladi (tone-mapping)"
    if not kind or hdr_kind(intro_v) == kind:
        return "", ""
    if not have_zscale:
        return "", "ffmpeg'da zscale filtri yo'q: reklama HDR ga o'tkazilmadi (ranglari kinodan farq qilishi mumkin)"
    trc = "smpte2084" if kind == "pq" else "arib-std-b67"
    if hdr_kind(intro_v):
        return "", "reklama boshqa HDR turida; o'zgartirilmaydi"
    mat = intro_v.get("color_space") if intro_v.get("color_space") in ("bt709", "bt470bg", "smpte170m") else "bt709"
    prim = intro_v.get("color_primaries") if intro_v.get("color_primaries") in ("bt709", "bt470bg", "smpte170m") else "bt709"
    rng = "pc" if intro_v.get("color_range") == "pc" else "tv"
    # setparams: reklama teglari noma'lum bo'lsa ham zscale ishlashi uchun kirish parametrlarini aniq belgilaydi
    f = ("setparams=colorspace=%s:color_primaries=%s:color_trc=bt709:range=%s,"
         "zscale=t=linear:npl=203,format=gbrpf32le,zscale=p=bt2020,zscale=t=%s:m=bt2020nc:r=limited"
         % (mat, prim, rng, trc))
    return f, "reklama SDR -> %s HDR (oq rang 203 nit) ga o'tkaziladi" % kind.upper()


def filter_available(ffmpeg, name):
    key = ("filter", name)
    if key not in _ENC_CACHE:
        try:
            r = subprocess.run([ffmpeg, "-hide_banner", "-filters"], capture_output=True, text=True,
                               encoding="utf-8", errors="replace", creationflags=NO_WINDOW)
            _ENC_CACHE[key] = re.search(r"\s%s\s" % re.escape(name), r.stdout) is not None
        except OSError:
            _ENC_CACHE[key] = False
    return _ENC_CACHE[key]


BASE = ["-y", "-nostdin", "-hide_banner", "-loglevel", "warning", "-progress", "pipe:1", "-nostats"]


def build_intro_cmd(ffmpeg, movie, intro, intro_path, out_path, iext, plan=None):
    """Reklama videoni kino parametrlariga moslab qayta kodlash buyrug'i."""
    mv = movie["video"]
    W, H = int(mv["width"]), int(mv["height"])
    fr = get_fps(mv)
    sar = get_sar(mv).replace(":", "/")

    vcodec = mv.get("codec_name")
    if vcodec not in VIDEO_ENC:
        raise RuntimeError("Bu video kodekni (%s) kodlash qo'llab-quvvatlanmaydi" % vcodec)
    venc = VIDEO_ENC[vcodec]
    if not encoder_available(ffmpeg, venc):
        if vcodec == "av1" and encoder_available(ffmpeg, "libaom-av1"):
            venc = "libaom-av1"
        else:
            raise RuntimeError("ffmpeg'da '%s' kodlovchisi yo'q" % venc)

    iv = intro["video"]
    flt = "flags=lanczos+accurate_rnd+full_chroma_int"
    pre = ""
    if get_sar(iv) != "1:1":
        pre = "scale=trunc(iw*sar/2)*2:ih:%s,setsar=1," % flt
    hdr_f, _ = hdr_filter(mv, iv, filter_available(ffmpeg, "zscale"))
    vf = (pre +
          "scale=%d:%d:force_original_aspect_ratio=increase:%s,"
          "crop=%d:%d,setsar=%s,fps=%d/%d,%sformat=%s"
          % (W, H, flt, W, H, sar, fr.numerator, fr.denominator,
             (hdr_f + ",") if hdr_f else "", mv.get("pix_fmt", "yuv420p")))

    cmd = [ffmpeg] + BASE + ["-i", intro_path]

    ma = movie["audio"]
    need_silence = bool(ma) and not intro["audio"]
    if need_silence:
        cmd += ["-f", "lavfi", "-t", "%.3f" % max(intro["duration"], 0.1),
                "-i", "anullsrc=channel_layout=stereo:sample_rate=48000"]

    cmd += ["-map", "0:%d" % iv["index"]]
    for _ in ma:
        if need_silence:
            cmd += ["-map", "1:a:0"]
        else:
            cmd += ["-map", "0:%d" % intro["audio"][0]["index"]]

    cmd += ["-vf", vf, "-c:v", venc]
    try:
        src_br = int(iv.get("bit_rate") or intro.get("bitrate") or 0)
    except ValueError:
        src_br = 0
    cap = max(src_br, 20000000)  # asl reklama bitreyti, kamida 20 Mbit/s
    rate = ["-maxrate", str(cap), "-bufsize", str(cap * 2)]
    if venc == "libx264":
        try:
            lim = h264_limits(int(mv.get("level") or 0), mv.get("profile"))
        except (TypeError, ValueError):
            lim = None
        if lim:
            mr = min(cap, lim[0])
            rate = ["-maxrate", str(mr), "-bufsize", str(min(mr * 2, lim[1]))]
        cmd += ["-preset", "slower", "-crf", "8", "-x264-params", "aq-mode=3"] + rate
        prof = h264_profile(mv.get("profile"))
        if prof:
            cmd += ["-profile:v", prof]
        try:
            lv = int(mv.get("level") or 0)
            if lv >= 10:
                cmd += ["-level:v", "%.1f" % (lv / 10.0)]
        except (TypeError, ValueError):
            pass
        try:
            refs = int(mv.get("refs") or 0)
            if refs > 0:
                cmd += ["-refs", str(min(refs, 16))]
        except (TypeError, ValueError):
            pass
    elif venc == "libx265":
        xp = ["aq-mode=3"] + (x265_hdr_params(mv) if hdr_kind(mv) == "pq" else [])
        cmd += ["-preset", "slow", "-crf", "10", "-x265-params", ":".join(xp)] + rate
    elif venc == "libvpx-vp9":
        cmd += ["-crf", "12", "-b:v", "0"]
    elif venc == "libvpx":
        cmd += ["-crf", "10", "-b:v", "2M"]
    elif venc in ("libsvtav1", "libaom-av1"):
        cmd += ["-crf", "22"] + (["-b:v", "0"] if venc == "libaom-av1" else [])
    elif venc == "mpeg4":
        cmd += ["-q:v", "1"]
    elif venc == "mpeg2video":
        cmd += ["-b:v", "8M"]

    if iext in MP4_EXTS:
        if venc == "libx265":
            cmd += ["-tag:v", "hvc1"]
        cmd += mp4_timescale_args(movie)

    for key, opt in (("color_space", "-colorspace"), ("color_primaries", "-color_primaries"),
                     ("color_transfer", "-color_trc"), ("color_range", "-color_range")):
        mval, ival = mv.get(key), iv.get(key)
        if mval and mval not in ("unknown", "reserved") and (bool(hdr_f) or not ival or ival in ("unknown", mval)):
            cmd += [opt, mval]

    plan = plan if plan is not None else audio_plan(ffmpeg, movie)
    for i, a in enumerate(ma):
        acodec = a.get("codec_name")
        aenc = plan[i]
        if aenc is None:
            # kinodagi bu trek uchun mos kodlovchi yo'q: shunchaki joy ushlovchi (dummy) trek.
            # Haqiqiy kino ovozi keyin to'g'ridan-to'g'ri kinoning o'zidan olinadi.
            cmd += ["-c:a:%d" % i, "aac", "-ar:a:%d" % i, "48000", "-ac:a:%d" % i, "1", "-b:a:%d" % i, "32000"]
            continue
        ch = int(a.get("channels", 2) or 2)
        cmd += ["-c:a:%d" % i, aenc,
                "-ar:a:%d" % i, str(a.get("sample_rate", 48000)),
                "-ac:a:%d" % i, str(ch)]
        if aenc == "libfdk_aac":
            cmd += ["-profile:a:%d" % i, "aac_he_v2" if "v2" in (a.get("profile") or "").lower() else "aac_he"]
        if acodec in LOSSY_AUDIO:
            try:
                br = int(a.get("bit_rate") or 0)
            except ValueError:
                br = 0
            if br <= 0:
                br = max(128, 64 * ch) * 1000
            cmd += ["-b:a:%d" % i, str(br)]
        if aenc in ("dca", "truehd"):
            cmd += ["-strict", "-2"]

    if ma:
        # audio 0 dan boshlanadi va video bilan bir xil uzunlikda tugaydi
        cmd += ["-af", "aresample=async=1:first_pts=0,apad", "-shortest"]
    else:
        cmd += ["-an"]
    cmd += ["-sn", "-dn", "-map_metadata", "-1", "-map_chapters", "-1", "-fflags", "+bitexact", out_path]
    return cmd


def build_remux_cmd(ffmpeg, movie, intro, intro_path, out_path, iext):
    """Mos reklamani kinoning konteyneriga QAYTA KODLAMASDAN ko'chirish (timebase tengligi uchun)."""
    cmd = [ffmpeg] + BASE + ["-i", intro_path, "-map", "0:%d" % intro["video"]["index"]]
    for a in intro["audio"]:
        cmd += ["-map", "0:%d" % a["index"]]
    cmd += ["-c", "copy", "-sn", "-dn", "-map_metadata", "-1", "-map_chapters", "-1", "-fflags", "+bitexact"]
    if iext in MP4_EXTS:
        if intro["video"].get("codec_name") == "hevc":
            cmd += ["-tag:v", "hvc1"]
        cmd += mp4_timescale_args(movie)
    cmd += [out_path]
    return cmd


INBAND_BSF = {"h264": "h264_mp4toannexb", "hevc": "hevc_mp4toannexb"}


def build_av_copy_cmd(ffmpeg, src, info, out_path, inband=False, extra=()):
    """Faqat video+audio ni (copy) MKV ga ko'chirish — timebase ni 1/1000 ga tenglashtiradi.
    inband=True: kinoning o'z SPS/PPS/VPS parametrlari har bir kalit kadr oldiga kadrlar ichiga qo'yiladi
    (kadr ma'lumotlari o'zgarmaydi), shunda reklamaning parametrlari kinoni buzmaydi."""
    cmd = [ffmpeg] + BASE + ["-i", src, "-map", "0:%d" % info["video"]["index"]]
    for a in info["audio"]:
        cmd += ["-map", "0:%d" % a["index"]]
    cmd += ["-c", "copy", "-sn", "-dn", "-map_metadata", "-1", "-map_chapters", "-1", "-fflags", "+bitexact"]
    if inband and INBAND_BSF.get(info["video"].get("codec_name")):
        cmd += ["-bsf:v", INBAND_BSF[info["video"]["codec_name"]]]
    cmd += list(extra) + [out_path]
    return cmd


def video_params_same(movie, other):
    """Ikkala videoning parametr to'plami (hvcC/avcC) bir xilmi."""
    a, b = movie["video"].get("_extra"), other["video"].get("_extra")
    return bool(a) and a == b


def concat_escape(p):
    return p.replace("\\", "/").replace("'", "'\\''")


def fix_rc(rc):
    return rc - (1 << 32) if rc > 0x7FFFFFFF else rc


# --------------------------------------------------------------------------
# Dastur oynasi
# --------------------------------------------------------------------------
#  Navbat (batch), avtomatik profil, sozlamalar
# --------------------------------------------------------------------------
VIDEO_EXTS = {".mp4", ".mkv", ".avi", ".mov", ".m4v", ".ts", ".m2ts", ".webm", ".flv", ".wmv", ".mpg", ".mpeg"}
SETTINGS_FILE = os.path.join(os.path.expanduser("~"), ".intro_joiner.json")


def ij_natural_key(p):
    """'Qism 2' 'Qism 10' dan oldin kelishi uchun tabiiy saralash."""
    return [int(t) if t.isdigit() else t.lower() for t in re.split(r"(\d+)", p)]


def fmt_size(n):
    return "%.1f GB" % (n / 2 ** 30) if n >= 2 ** 30 else "%.0f MB" % (n / 2 ** 20)


def fmt_dur(sec):
    sec = int(sec)
    h, r = divmod(sec, 3600)
    m, s_ = divmod(r, 60)
    return ("%d s %02d min" % (h, m)) if h else ("%d min %02d s" % (m, s_))


def collect_videos(folder, recursive=True, suffix=""):
    """Papkadagi video fayllar (tabiiy tartibda). Oldingi natijalar (nom oxiri = suffix) va vaqtinchalik fayllar o'tkaziladi."""
    found = []
    for root, dirs, files in os.walk(folder):
        dirs[:] = [d for d in dirs if not d.startswith(".introjoin_")] if recursive else []
        for f in files:
            stem, ext = os.path.splitext(f)
            if ext.lower() not in VIDEO_EXTS or stem.endswith(".part") or f.startswith("."):
                continue
            if suffix and stem.endswith(suffix):
                continue
            found.append(os.path.join(root, f))
    return sorted(found, key=ij_natural_key)


def plan_outputs(items, outdir, suffix, reserved=()):
    """Har bir kino uchun natija yo'li. Kirish fayllarini va bir-birini hech qachon bosib yozmaydi."""
    norm = lambda x: os.path.normcase(os.path.abspath(x))  # noqa: E731
    used = {norm(r) for r in reserved}
    outs = []
    for it in items:
        src = it["path"]
        base, ext = os.path.splitext(os.path.basename(src))
        d = os.path.dirname(os.path.abspath(src))
        if outdir:
            d = outdir
            if it.get("root"):
                rel = os.path.relpath(os.path.dirname(os.path.abspath(src)), it["root"])
                if rel != ".":
                    d = os.path.join(outdir, rel)
        cand, n = os.path.join(d, base + suffix + ext), 2
        while norm(cand) in used:
            cand = os.path.join(d, "%s%s (%d)%s" % (base, suffix, n, ext))
            n += 1
        used.add(norm(cand))
        outs.append(cand)
    return outs


_V_KEYS = ("codec_name", "profile", "level", "width", "height", "pix_fmt", "time_base", "color_space",
           "color_primaries", "color_transfer", "color_range", "field_order")
_A_KEYS = ("codec_name", "profile", "sample_rate", "channels", "channel_layout", "time_base")


def intro_cache_key(movie, iext, plan, encode):
    """Reklama tayyorlanishiga ta'sir qiladigan kino parametrlari. Bir xil bo'lsa (serial qismlari) reklama qayta kodlanmaydi.
    Qismlar orasida o'zgarib turadigan maydonlar (bitreyt, davomiylik, refs, kadr soni...) hisobga olinmaydi."""
    v = movie["video"]
    key = {"v": {k: v.get(k) for k in _V_KEYS}, "fps": str(get_fps(v)), "sar": get_sar(v),
           "hdr": [hdr_kind(v), x265_hdr_params(v)], "a": [], "ext": iext, "plan": list(plan), "enc": bool(encode)}
    for a in movie["audio"]:
        d = {k: a.get(k) for k in _A_KEYS}
        try:
            d["br"] = round(int(a.get("bit_rate") or 0) / 32000.0)
        except ValueError:
            d["br"] = 0
        key["a"].append(d)
    return json.dumps(key, sort_keys=True, default=str)


def auto_profile(movie):
    """Kino tahlili asosida avtomatik tanlangan sozlamalar haqida qisqa xulosa (log uchun)."""
    v = movie["video"]
    codec = v.get("codec_name")
    pf = v.get("pix_fmt") or ""
    depth = "12-bit" if "12" in pf else ("10-bit" if "10" in pf else "8-bit")
    hdr = {"pq": "HDR10", "hlg": "HLG"}.get(hdr_kind(v))
    if _side(v, "DOVI configuration record"):
        hdr = (hdr + " + Dolby Vision") if hdr else "Dolby Vision"
    enc = {"h264": "x264 (CRF 8, preset slower, kino level/profile/refs bo'yicha)",
           "hevc": "x265 (CRF 10, preset slow, %s%s)" % (depth, ", HDR metadata bilan" if hdr_kind(v) == "pq" else ""),
           "vp9": "libvpx-vp9 (CRF 12)", "vp8": "libvpx (CRF 10)", "av1": "AV1 (CRF 22)",
           "mpeg4": "mpeg4 (q=1)", "mpeg2video": "mpeg2 (8 Mbit/s)"}.get(codec, str(codec))
    kinds = {}
    for x in movie["subs"]:
        kinds[x.get("codec_name", "?")] = kinds.get(x.get("codec_name", "?"), 0) + 1
    na = len(movie["audio"])
    lines = ["AVTO-PROFIL: %s %s %dx%d, %s%s | audio: %s | subtitr: %s | boblar: %d, shriftlar: %d"
             % ((codec or "?").upper(), depth, int(v.get("width", 0)), int(v.get("height", 0)),
                "%.3f fps" % float(get_fps(v)), (", " + hdr) if hdr else "",
                ("%d ta trek (har biri alohida moslanadi)" % na) if na > 1 else ("1 ta trek" if na else "yo'q"),
                ", ".join("%s x%d" % kv for kv in kinds.items()) if kinds else "yo'q",
                len(movie["chapters"]), len(movie["attach"])),
             "  -> reklama kodlovchisi: " + enc]
    if hdr and "Dolby" in hdr:
        lines.append("  -> Dolby Vision kinoda bor: kinoning o'zi o'zgarmaydi, reklama oddiy %s shaklida qo'shiladi."
                     % (hdr_kind(v) or "SDR").upper())
    return lines


def load_settings():
    try:
        with open(SETTINGS_FILE, encoding="utf-8") as f:
            d = json.load(f)
            return d if isinstance(d, dict) else {}
    except (OSError, ValueError):
        return {}


def save_settings(d):
    try:
        with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
            json.dump(d, f, ensure_ascii=False, indent=1)
    except OSError:
        pass



# --------------------------------------------------------------------------


def make_intro_window(tk, ttk, filedialog, messagebox, T):
    """Intro Qo'shuvchi — dastur ichidagi alohida oyna (Toplevel)."""
    BG, CARD, FG, MUTED, ACC = T["BG"], T["CARD"], T["FG"], T["MUTED"], T["ACC"]

    class IntroWindow(tk.Toplevel):
        def __init__(self, master):
            super().__init__(master)
            self.title("Intro Qo'shuvchi — kino va seriallar boshiga reklama")
            self.configure(bg=BG)
            self.geometry("1040x860")
            self.minsize(900, 680)
            try:
                self.iconphoto(False, logo_image(64, self))
            except Exception:
                pass
            self.q = queue.Queue()
            self.stop_evt = threading.Event()
            self.skip_evt = threading.Event()
            self.proc = None
            self.worker = None
            self.ts_warn = 0
            self.items = []          # {"id", "path", "root", "size", "state", "out"}
            self._next_id = 1
            self.batch_i, self.batch_n = 0, 1
            self.cur_iid = None
            self.running = False

            cfg = load_settings()
            self.var_intro = tk.StringVar(value=cfg.get("intro", ""))
            self.var_outdir = tk.StringVar(value=cfg.get("outdir", ""))
            self.var_suffix = tk.StringVar(value=cfg.get("suffix", "_intro"))
            self.var_keep = tk.BooleanVar(value=cfg.get("keep", True))
            self.var_skip = tk.BooleanVar(value=cfg.get("skip_existing", True))
            self.var_rec = tk.BooleanVar(value=cfg.get("recursive", True))
            self.var_verbose = tk.BooleanVar(value=cfg.get("verbose", False))
            self.verbose = bool(self.var_verbose.get())
            self.var_status = tk.StringVar(value="Tayyor")
            self.var_queue = tk.StringVar(value="Navbat bo'sh")
            self._last_dir = cfg.get("last_dir", "")

            self._build()
            self.protocol("WM_DELETE_WINDOW", self._on_close)
            self.after(100, self._poll)

        # ---- interfeys ----
        def _ib(self, parent, text, icon, cmd, style="TButton", width=None):
            b = ttk.Button(parent, text=" " + text, image=icon_image(icon, 18, "#ffffff" if style != "TButton" else FG, self),
                           compound="left", command=cmd, style=style)
            if width:
                b.configure(width=width)
            return b

        def _build(self):
            pad = {"padx": 6, "pady": 4}
            hd = tk.Frame(self, bg="#23252f")
            hd.pack(fill="x")
            tk.Label(hd, image=logo_image(48, self), bg="#23252f").pack(side="left", padx=(16, 10), pady=10)
            tx = tk.Frame(hd, bg="#23252f")
            tx.pack(side="left", pady=8)
            tk.Label(tx, text="Intro Qo'shuvchi", bg="#23252f", fg="white", font=("Segoe UI", 16, "bold")).pack(anchor="w")
            tk.Label(tx, text="Kino va seriallar boshiga reklama (intro) — kino sifati o'zgarmaydi (-c copy)",
                     bg="#23252f", fg=MUTED, font=("Segoe UI", 9)).pack(anchor="w")
            tk.Frame(self, bg=ACC, height=2).pack(fill="x")

            top = ttk.LabelFrame(self, text="Sozlamalar")
            top.pack(fill="x", padx=12, pady=(10, 4))
            top.columnconfigure(1, weight=1)
            ttk.Label(top, text="Reklama video:").grid(row=0, column=0, sticky="w", **pad)
            ttk.Entry(top, textvariable=self.var_intro).grid(row=0, column=1, sticky="ew", **pad)
            self._ib(top, "Tanlash...", "film", self.pick_intro).grid(row=0, column=2, **pad)
            ttk.Label(top, text="Natija papkasi:").grid(row=1, column=0, sticky="w", **pad)
            ttk.Entry(top, textvariable=self.var_outdir).grid(row=1, column=1, sticky="ew", **pad)
            self._ib(top, "Tanlash...", "folder", self.pick_outdir).grid(row=1, column=2, **pad)
            ttk.Label(top, text="(bo'sh bo'lsa — har bir natija o'z kinosi yonida saqlanadi)",
                      style="Muted.TLabel").grid(row=2, column=1, sticky="w", padx=6)
            ttk.Label(top, text="Nom oxiri:").grid(row=3, column=0, sticky="w", **pad)
            sf = ttk.Frame(top)
            sf.grid(row=3, column=1, sticky="w", **pad)
            ttk.Entry(sf, textvariable=self.var_suffix, width=18).pack(side="left")
            ttk.Label(sf, text="  masalan: Kino.mkv  →  Kino_intro.mkv", style="Muted.TLabel").pack(side="left")

            qf = ttk.LabelFrame(self, text="Navbat — kinolar / serial qismlari (tepadan pastga ketma-ket ishlanadi)")
            qf.pack(fill="both", expand=True, padx=12, pady=4)
            qf.columnconfigure(0, weight=1)
            qf.rowconfigure(0, weight=1)
            cols = ("n", "name", "size", "state")
            self.tree = ttk.Treeview(qf, columns=cols, show="headings", selectmode="extended", height=9)
            for c, t, w, anc in (("n", "№", 40, "center"), ("name", "Fayl", 380, "w"),
                                 ("size", "Hajmi", 80, "e"), ("state", "Holat", 240, "w")):
                self.tree.heading(c, text=t)
                self.tree.column(c, width=w, anchor=anc, stretch=(c in ("name", "state")))
            sb = ttk.Scrollbar(qf, command=self.tree.yview)
            self.tree.configure(yscrollcommand=sb.set)
            self.tree.grid(row=0, column=0, sticky="nsew", padx=(6, 0), pady=6)
            sb.grid(row=0, column=1, sticky="ns", pady=6)
            self.tree.tag_configure("ok", foreground="#4ade80")
            self.tree.tag_configure("fail", foreground="#f87171")
            self.tree.tag_configure("run", foreground="#60a5fa")
            self.tree.tag_configure("skip", foreground="#fbbf24")
            self.tree.bind("<Delete>", lambda _e: self.remove_selected())

            bf = ttk.Frame(qf)
            bf.grid(row=0, column=2, sticky="ns", padx=6, pady=6)
            self.q_buttons = []
            for text, icon, cmd in (("Fayl(lar)...", "plus", self.add_files), ("Papka (serial)...", "folder", self.add_folder),
                                    ("Olib tashlash", "trash", self.remove_selected), ("Tozalash", "queue", self.clear_queue),
                                    ("Yuqoriga", "up", lambda: self.move_selected(-1)), ("Pastga", "down", lambda: self.move_selected(1))):
                b = self._ib(bf, text, icon, cmd, width=18)
                b.pack(pady=2)
                self.q_buttons.append(b)
            ttk.Checkbutton(bf, variable=self.var_rec, text="Papka ichidagilar\nham (Season...)").pack(pady=(8, 0), anchor="w")
            ttk.Label(qf, textvariable=self.var_queue, style="Muted.TLabel").grid(row=1, column=0, columnspan=3,
                                                                                   sticky="w", padx=8, pady=(0, 4))

            of = ttk.Frame(self)
            of.pack(fill="x", padx=12)
            ttk.Checkbutton(
                of, variable=self.var_keep,
                text="Kino konteynerini aynan saqlash (tavsiya: hamma audio/subtitr nomlari, boblar, shriftlar o'zgarmaydi)"
            ).pack(anchor="w")
            ttk.Checkbutton(of, variable=self.var_verbose,
                            text="Batafsil log (texnik tafsilotlar; oddiy holatda kerak emas)").pack(anchor="w")
            ttk.Checkbutton(of, variable=self.var_skip,
                            text="Natija fayli allaqachon bor bo'lsa — o'tkazib yuborish (o'chirilsa, almashtiriladi)"
                            ).pack(anchor="w")

            bar = ttk.Frame(self)
            bar.pack(fill="x", padx=12, pady=(8, 0))
            self.btn_start = self._ib(bar, "START", "play", self.start, "Accent.TButton")
            self.btn_start.pack(side="left", padx=(0, 6), pady=4)
            self.btn_stop = self._ib(bar, "STOP (hammasini)", "stop", self.stop, "Stop.TButton")
            self.btn_stop.configure(state="disabled")
            self.btn_stop.pack(side="left", padx=6, pady=4)
            self.btn_skip = self._ib(bar, "Joriysini o'tkazish", "skip", self.skip_current)
            self.btn_skip.configure(state="disabled")
            self.btn_skip.pack(side="left", padx=6, pady=4)

            ttk.Label(self, text="Joriy fayl:", style="Muted.TLabel").pack(anchor="w", padx=14)
            self.progress = ttk.Progressbar(self, maximum=100)
            self.progress.pack(fill="x", padx=14, pady=(0, 3))
            ttk.Label(self, text="Butun navbat:", style="Muted.TLabel").pack(anchor="w", padx=14)
            self.progress_all = ttk.Progressbar(self, maximum=100)
            self.progress_all.pack(fill="x", padx=14, pady=(0, 2))
            ttk.Label(self, textvariable=self.var_status).pack(anchor="w", padx=14)

            ttk.Label(self, text="Log", style="Muted.TLabel").pack(anchor="w", padx=14, pady=(6, 0))
            lf = ttk.Frame(self)
            lf.pack(fill="both", expand=True, padx=14, pady=(2, 12))
            self.txt = tk.Text(lf, height=10, wrap="word", state="disabled", bg="#14151a", fg=FG, relief="flat", highlightthickness=1, highlightbackground="#3a3d4c", highlightcolor=ACC,
                               font=("Consolas", 10), insertbackground=FG, padx=8, pady=6)
            sb2 = ttk.Scrollbar(lf, command=self.txt.yview)
            self.txt.configure(yscrollcommand=sb2.set)
            self.txt.pack(side="left", fill="both", expand=True)
            sb2.pack(side="right", fill="y")

        # ---- navbat ----
        def _set_running(self, running):
            self.running = running
            for b in self.q_buttons:
                b.configure(state="disabled" if running else "normal")
            self.btn_start.configure(state="disabled" if running else "normal")
            self.btn_stop.configure(state="normal" if running else "disabled")
            self.btn_skip.configure(state="normal" if running else "disabled")

        def _redraw(self, keep_sel=()):
            self.tree.delete(*self.tree.get_children())
            for n, it in enumerate(self.items, 1):
                self.tree.insert("", "end", iid=str(it["id"]), tags=(it.get("tag", ""),),
                                 values=(n, it["path"], fmt_size(it["size"]), it["state"]))
            for iid in keep_sel:
                if self.tree.exists(iid):
                    self.tree.selection_add(iid)
            tot = sum(i["size"] for i in self.items)
            self.var_queue.set("Navbatda: %d ta fayl, jami %s" % (len(self.items), fmt_size(tot)) if self.items
                               else "Navbat bo'sh — fayl yoki papka (serial) qo'shing")

        def _add_paths(self, paths, root=None):
            have = {os.path.normcase(os.path.abspath(i["path"])) for i in self.items}
            intro = self.var_intro.get().strip()
            if intro:
                have.add(os.path.normcase(os.path.abspath(intro)))
            added = 0
            for p in paths:
                key = os.path.normcase(os.path.abspath(p))
                if key in have or not os.path.isfile(p):
                    continue
                have.add(key)
                try:
                    size = os.path.getsize(p)
                except OSError:
                    size = 0
                self.items.append({"id": self._next_id, "path": os.path.abspath(p), "root": root,
                                   "size": size, "state": "Kutilmoqda", "tag": ""})
                self._next_id += 1
                added += 1
            self._redraw()
            return added

        def add_files(self):
            ps = filedialog.askopenfilenames(title="Kino(lar)ni tanlang", filetypes=VIDEO_TYPES,
                                             initialdir=self._last_dir or None)
            if ps:
                self._last_dir = os.path.dirname(ps[0])
                self._add_paths(sorted(ps, key=ij_natural_key))

        def add_folder(self):
            d = filedialog.askdirectory(title="Serial/kinolar papkasini tanlang", initialdir=self._last_dir or None)
            if not d:
                return
            self._last_dir = d
            found = collect_videos(d, self.var_rec.get(), self.var_suffix.get().strip())
            n = self._add_paths(found, root=os.path.abspath(d))
            self.log("Papka: %s — %d ta video topildi, %d tasi navbatga qo'shildi." % (d, len(found), n))
            if not found:
                messagebox.showinfo("Bo'sh", "Bu papkada video fayl topilmadi.")

        def remove_selected(self):
            if self.running:
                return
            sel = {int(i) for i in self.tree.selection()}
            self.items = [i for i in self.items if i["id"] not in sel]
            self._redraw()

        def clear_queue(self):
            if self.running:
                return
            self.items = []
            self._redraw()

        def move_selected(self, delta):
            if self.running:
                return
            sel = {int(i) for i in self.tree.selection()}
            its = self.items
            rng = range(len(its)) if delta < 0 else range(len(its) - 1, -1, -1)
            for i in rng:
                j = i + delta
                if its[i]["id"] in sel and 0 <= j < len(its) and its[j]["id"] not in sel:
                    its[i], its[j] = its[j], its[i]
            self._redraw([str(i) for i in sel])

        def pick_intro(self):
            p = filedialog.askopenfilename(title="Reklama videoni tanlang", filetypes=VIDEO_TYPES)
            if p:
                self.var_intro.set(p)

        def pick_outdir(self):
            d = filedialog.askdirectory(title="Natijalar saqlanadigan papka")
            if d:
                self.var_outdir.set(d)

        # ---- log / holat ----
        def log(self, msg):
            self.q.put(("log", msg))

        def vlog(self, msg):
            """Faqat 'Batafsil log' yoqilganda ko'rinadigan texnik xabar."""
            if getattr(self, "verbose", True):
                self.log(msg)

        def _poll(self):
            try:
                while True:
                    kind, val = self.q.get_nowait()
                    if kind == "log":
                        self.txt.configure(state="normal")
                        self.txt.insert("end", val + "\n")
                        self.txt.see("end")
                        self.txt.configure(state="disabled")
                    elif kind == "progress":
                        self.progress["value"] = val
                        self.progress_all["value"] = (self.batch_i + val / 100.0) / max(1, self.batch_n) * 100
                        self.var_status.set("[%d/%d] Jarayon: %.1f%%" % (self.batch_i + 1, self.batch_n, val))
                    elif kind == "status":
                        self.var_status.set(val)
                    elif kind == "batch":
                        self.batch_i, self.batch_n = val
                        self.progress["value"] = 0
                    elif kind == "row":
                        iid, state, tag = val
                        for it in self.items:
                            if str(it["id"]) == iid:
                                it["state"], it["tag"] = state, tag
                        if self.tree.exists(iid):
                            self.tree.set(iid, "state", state)
                            self.tree.item(iid, tags=(tag,))
                            self.tree.see(iid)
                        self.cur_iid = iid if tag == "run" else self.cur_iid
                    elif kind == "outpath":
                        pass  # natija yo'li log orqali ko'rsatiladi
                    elif kind == "done":
                        self._set_running(False)
                        ok, msg = val
                        self.var_status.set(msg)
                        self.progress["value"] = 100 if ok else 0
                        if ok:
                            self.progress_all["value"] = 100
            except queue.Empty:
                pass
            self.after(100, self._poll)

        # ---- start / stop ----
        def start(self):
            intro = self.var_intro.get().strip()
            if not self.items:
                messagebox.showwarning("Xato", "Navbat bo'sh. Kamida bitta kino (yoki serial papkasini) qo'shing.")
                return
            if not os.path.isfile(intro):
                messagebox.showwarning("Xato", "Reklama videoni tanlang.")
                return
            outdir = self.var_outdir.get().strip()
            suffix = self.var_suffix.get()
            missing = [i["path"] for i in self.items if not os.path.isfile(i["path"])]
            if missing:
                messagebox.showwarning("Xato", "Quyidagi fayl topilmadi (navbatdan olib tashlang):\n%s" % missing[0])
                return
            if any(os.path.normcase(os.path.abspath(i["path"])) == os.path.normcase(os.path.abspath(intro))
                   for i in self.items):
                messagebox.showwarning("Xato", "Reklama videoning o'zi navbatda turibdi. Uni navbatdan olib tashlang.")
                return
            outs = plan_outputs(self.items, outdir, suffix, [i["path"] for i in self.items] + [intro])
            keep_container = bool(self.var_keep.get())
            skip_existing = bool(self.var_skip.get())
            if keep_container:
                ffprobe = find_tool("ffprobe")
                if ffprobe:
                    outs = [resolve_out_path(ffprobe, it["path"], o) for it, o in zip(self.items, outs)]
            if not skip_existing:
                ex = [o for o in outs if os.path.exists(o)]
                if ex and not messagebox.askyesno(
                        "Fayllar mavjud", "%d ta natija fayli allaqachon bor (masalan:\n%s).\n\nAlmashtirilsinmi?"
                        % (len(ex), ex[0])):
                    return
            save_settings({"intro": intro, "outdir": outdir, "suffix": suffix, "keep": keep_container,
                           "skip_existing": skip_existing, "recursive": bool(self.var_rec.get()),
                           "verbose": bool(self.var_verbose.get()), "last_dir": self._last_dir})
            self.verbose = bool(self.var_verbose.get())
            for it in self.items:
                it["state"], it["tag"] = "Kutilmoqda", ""
            self._redraw(self.tree.selection())
            jobs = [(str(it["id"]), it["path"], o) for it, o in zip(self.items, outs)]
            self.stop_evt.clear()
            self.skip_evt.clear()
            self.progress["value"] = 0
            self.progress_all["value"] = 0
            self.batch_i, self.batch_n = 0, len(jobs)
            self._set_running(True)
            self.worker = threading.Thread(target=self._batch, args=(jobs, intro, keep_container, skip_existing),
                                           daemon=True)
            self.worker.start()

        def stop(self):
            self.stop_evt.set()
            self.log("To'xtatilmoqda (butun navbat)...")
            self._kill_proc()

        def skip_current(self):
            self.skip_evt.set()
            self.log("Joriy fayl o'tkazib yuborilmoqda...")
            self._kill_proc()

        def _kill_proc(self):
            p = self.proc
            if p and p.poll() is None:
                try:
                    p.terminate()
                except OSError:
                    pass

        def _on_close(self):
            if self.worker and self.worker.is_alive():
                if not messagebox.askyesno("Chiqish", "Jarayon ketmoqda. To'xtatib chiqilsinmi?"):
                    return
                self.stop()
                self.worker.join(timeout=8)
            save_settings({"intro": self.var_intro.get().strip(), "outdir": self.var_outdir.get().strip(),
                           "suffix": self.var_suffix.get(), "keep": bool(self.var_keep.get()),
                           "skip_existing": bool(self.var_skip.get()), "recursive": bool(self.var_rec.get()),
                           "verbose": bool(self.var_verbose.get()), "last_dir": self._last_dir})
            self.destroy()

        def _cancel_requested(self):
            sk = getattr(self, "skip_evt", None)
            return self.stop_evt.is_set() or (sk is not None and sk.is_set())

        # ---- ffmpeg ishga tushirish ----
        def _ffmpeg(self, cmd, total, lo, hi):
            if self._cancel_requested():
                raise IJCancelled()
            self.proc = subprocess.Popen(
                cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                text=True, encoding="utf-8", errors="replace", bufsize=1, creationflags=NO_WINDOW)
            seen = {}
            for line in self.proc.stdout:
                line = line.strip()
                if not line:
                    continue
                if PROGRESS_KEYS.match(line):
                    if line.startswith("out_time_us=") or line.startswith("out_time_ms="):
                        try:
                            t = int(line.split("=", 1)[1]) / 1e6
                            if total > 0:
                                self.q.put(("progress", lo + (hi - lo) * min(1.0, max(0.0, t / total))))
                        except ValueError:
                            pass
                    continue
                if "New subtitle stream with index" in line:
                    continue  # concat kinodagi subtitr oqimlarini topgani haqida zararsiz xabar
                if ("Attachment" in line and "Could not find codec parameters" in line) \
                        or line.startswith("Consider increasing the value for the 'analyzeduration'"):
                    continue  # shrift ilovalari (MKV attachment) haqida zararsiz xabar
                # bir xil xabar yuzlab marta takrorlansa, logni to'ldirib yubormaslik uchun
                sig = re.sub(r"0x[0-9a-fA-F]+|\d+", "#", line)
                seen[sig] = seen.get(sig, 0) + 1
                if any(k in line for k in TS_WARN):
                    self.ts_warn += 1       # vaqt belgisi ogohlantirishlari sanaladi, oxirida bitta qatorda xabar beriladi
                    if seen[sig] <= 2:
                        self.vlog(line)
                    continue
                if ENC_STATS.match(line):
                    self.vlog(line)
                    continue
                if seen[sig] <= 2:
                    self.log(line)
            rc = self.proc.wait()
            self.proc = None
            for sig, n in seen.items():
                if n > 2:
                    self.vlog("   (... shunga o'xshash yana %d ta xabar yashirildi)" % (n - 2))
            if self._cancel_requested():
                raise IJCancelled()
            if rc != 0:
                raise RuntimeError("ffmpeg xato bilan tugadi (kod %d). Yuqoridagi logga qarang." % fix_rc(rc))
            self.q.put(("progress", hi))

        # ---- navbatni ketma-ket ishlov berish ----
        def _batch(self, jobs, intro_path, keep_container, skip_existing):
            cache = {"dir": None, "items": {}}
            n = len(jobs)
            res = {"ok": [], "fail": [], "skip": [], "stop": []}
            t0 = time.time()
            try:
                if n > 1:
                    self.log("Navbat boshlandi: %d ta fayl." % n)
                    self.vlog("Reklama bir xil parametrli kinolar (serial qismlari) uchun bir marta tayyorlanadi.")
                for i, (iid, movie, out) in enumerate(jobs):
                    if self.stop_evt.is_set():
                        break
                    self.skip_evt.clear()
                    self.q.put(("batch", (i, n)))
                    self.q.put(("row", (iid, "Ishlanmoqda...", "run")))
                    self.log("")
                    self.log("═══ [%d/%d] %s ═══" % (i + 1, n, os.path.basename(movie)))
                    t1 = time.time()
                    r = self._process(movie, intro_path, out, keep_container, cache, skip_existing)
                    took = fmt_dur(time.time() - t1)
                    if r[0] == "ok":
                        res["ok"].append(movie)
                        self.q.put(("row", (iid, "✔ Tayyor (%.0f MB, %s)" % (r[2], took), "ok")))
                    elif r[0] == "skip":
                        res["skip"].append(movie)
                        self.q.put(("row", (iid, "↷ O'tkazildi: %s" % r[2], "skip")))
                    elif r[0] == "stop":
                        if self.stop_evt.is_set():
                            res["stop"].append(movie)
                            self.q.put(("row", (iid, "■ To'xtatildi", "skip")))
                            break
                        res["skip"].append(movie)
                        self.q.put(("row", (iid, "↷ Foydalanuvchi o'tkazib yubordi", "skip")))
                    else:
                        res["fail"].append((movie, (r[1].strip().splitlines() or [""])[0][:200]))
                        self.q.put(("row", (iid, "✘ Xato: %s" % (r[1].strip().splitlines() or [""])[0][:90], "fail")))
                self.log("")
                self.log("═══ YAKUN (%s) ═══" % fmt_dur(time.time() - t0))
                self.log("Tayyor: %d | Xato: %d | O'tkazildi: %d%s"
                         % (len(res["ok"]), len(res["fail"]), len(res["skip"]),
                            " | To'xtatildi" if res["stop"] else ""))
                for m, why in res["fail"]:
                    self.log("  ✘ %s — %s" % (os.path.basename(m), why))
                stopped = self.stop_evt.is_set()
                ok = not res["fail"] and not stopped
                msg = "To'xtatildi" if stopped else (
                    "Tayyor ✔ (%d ta)" % len(res["ok"]) if ok else
                    "Tugadi: %d tayyor, %d xato" % (len(res["ok"]), len(res["fail"])))
                self.q.put(("done", (ok, msg)))
            except Exception as e:  # noqa: BLE001
                self.log("XATO (navbat): %s" % e)
                self.q.put(("done", (False, "Xato yuz berdi")))
            finally:
                if cache["dir"]:
                    shutil.rmtree(cache["dir"], ignore_errors=True)

        # ---- bitta kinoni ishlash ----
        def _run(self, movie_path, intro_path, out_path, keep_container=True):
            """Bitta fayl uchun (sinov/skript uchun qulay qobiq)."""
            r = self._process(movie_path, intro_path, out_path, keep_container)
            if r[0] == "ok":
                self.q.put(("done", (True, "Tayyor ✔")))
            elif r[0] == "stop":
                self.q.put(("done", (False, "To'xtatildi")))
            else:
                self.q.put(("done", (False, "Xato yuz berdi" if r[0] == "fail" else "O'tkazildi")))

        def _process(self, movie_path, intro_path, out_path, keep_container=True, cache=None, skip_existing=False):
            """Qaytaradi: ("ok", yo'l, MB) | ("skip", yo'l, sabab) | ("stop", "") | ("fail", xabar)."""
            tmpdir, part = None, None
            self.ts_warn = 0
            try:
                ffmpeg, ffprobe = find_tool("ffmpeg"), find_tool("ffprobe")
                if not ffmpeg or not ffprobe:
                    raise RuntimeError("ffmpeg/ffprobe topilmadi. Ularni o'rnating (PATH ga qo'shing) "
                                       "yoki shu skript yoniga qo'ying.")

                movie = ij_probe(ffprobe, movie_path)
                intro = ij_probe(ffprobe, intro_path)
                if getattr(self, "verbose", True):
                    self.log("KINO  -> " + describe(movie))
                    self.log("REKLAMA -> " + describe(intro))
                    for line in auto_profile(movie):
                        self.log(line)
                else:
                    self.log("Kino: " + short_desc(movie))

                # ---- chiqish konteyneri ----
                ext = os.path.splitext(out_path)[1].lower()
                if not ext:
                    ext = os.path.splitext(movie_path)[1].lower() or ".mkv"
                    out_path += ext
                if keep_container:
                    rext = real_container_ext(movie, ext)
                    if rext and rext != ext:
                        new_path = os.path.splitext(out_path)[0] + rext
                        self.vlog("Kino aslida %s konteynerida (fayl kengaytmasi %s bo'lsa ham). Hech narsa o'zgarmasligi uchun "
                                 "natija ham shu konteynerda saqlanadi: %s" % (rext.upper().lstrip("."), ext, new_path))
                        out_path, ext = new_path, rext
                        self.q.put(("outpath", out_path))
                bad = container_problems(movie, ext)
                if bad:
                    new_path = os.path.splitext(out_path)[0] + ".mkv"
                    self.log("Kinodagi %s %s ga sig'maydi, shuning uchun natija MKV ko'rinishida saqlanadi: %s"
                             % (", ".join(sorted(set(bad))), ext, new_path))
                    out_path, ext = new_path, ".mkv"
                if skip_existing and os.path.exists(out_path):
                    self.log("Natija fayli allaqachon bor — o'tkazib yuborildi: %s" % out_path)
                    return ("skip", out_path, "natija allaqachon bor")

                out_dir = os.path.dirname(os.path.abspath(out_path))
                os.makedirs(out_dir, exist_ok=True)
                need = os.path.getsize(movie_path) + 3 * os.path.getsize(intro_path) + (200 << 20)
                if shutil.disk_usage(out_dir).free < need:
                    raise RuntimeError("Saqlash diskida joy yetarli emas (kamida %.1f GB kerak)." % (need / 2 ** 30))
                tmpdir = tempfile.mkdtemp(prefix=".introjoin_", dir=out_dir)
                part = os.path.join(out_dir, os.path.splitext(os.path.basename(out_path))[0] + ".part" + ext)

                # ---- reklamani tayyorlash (kinoning konteyneri shaklida) ----
                iext = intro_container(movie)
                fixed0 = os.path.join(tmpdir, "intro_fixed" + iext)
                ma = movie["audio"]
                plan = audio_plan(ffmpeg, movie)
                diffs = compare(movie, intro)
                for i, enc in enumerate(plan):
                    if enc is None:
                        diffs.append("audio#%d (%s) uchun mos kodlovchi yo'q" % (i, audio_label(ma[i])))
                hf, hnote = hdr_filter(movie["video"], intro["video"], filter_available(ffmpeg, "zscale"))
                if hnote:
                    self.log("HDR: " + hnote)
                if hf:
                    diffs.append("dinamik diapazon (HDR/SDR) farq qiladi")

                def make_intro(do_encode, cur_plan):
                    """Reklamani tayyorlaydi; navbatda bir xil parametrli kinolar uchun avval tayyorlanganini qaytaradi."""
                    key = intro_cache_key(movie, iext, cur_plan, do_encode) if cache is not None else None
                    if key and key in cache["items"] and os.path.exists(cache["items"][key][0]):
                        self.log("Reklama: bir xil parametrli avvalgi nusxa ishlatiladi (qayta kodlanmaydi) ✔")
                        self.q.put(("progress", 10))
                        return cache["items"][key]
                    dst = fixed0
                    if key:
                        if not cache["dir"]:
                            cache["dir"] = tempfile.mkdtemp(prefix=".introjoin_cache_", dir=out_dir)
                        dst = os.path.join(cache["dir"], "intro_%d%s" % (len(cache["items"]), iext))
                    if do_encode:
                        cmd = build_intro_cmd(ffmpeg, movie, intro, intro_path, dst, iext, cur_plan)
                        self.vlog("Reklama qayta kodlanmoqda...")
                    else:
                        cmd = build_remux_cmd(ffmpeg, movie, intro, intro_path, dst, iext)
                    self._ffmpeg(cmd, intro["duration"], 0, 10)
                    res = (dst, ij_probe(ffprobe, dst))
                    if key:
                        cache["items"][key] = res
                    return res

                encode = bool(diffs)
                if encode:
                    why = ", ".join(dict.fromkeys(d.split(":")[0].split(" uchun ")[0] for d in diffs))
                    self.log("Reklama kinoga moslanadi (farq: %s)" % why)
                    for d in diffs:
                        self.vlog("  - " + d)
                else:
                    self.log("Reklama kinoga to'liq mos — qayta kodlanmaydi.")
                try:
                    fixed, fixed_info = make_intro(encode, plan)
                except RuntimeError:
                    if "libfdk_aac" not in plan:
                        raise
                    self.log("libfdk_aac bilan kodlab bo'lmadi; HE-AAC trek uchun kino ovozi to'g'ridan-to'g'ri olinadi.")
                    plan = [None if e == "libfdk_aac" else e for e in plan]
                    encode = True
                    fixed, fixed_info = make_intro(True, plan)

                def bad_tracks():
                    return {i for i in range(len(ma))
                            if plan[i] is None or i >= len(fixed_info["audio"])
                            or not audio_params_match(ma[i], fixed_info["audio"][i])}

                offs = bad_tracks()
                if offs and not encode:
                    self.log("Reklama audiosining konfiguratsiyasi kinoniki bilan bir xil emas, qayta kodlanadi...")
                    encode = True
                    fixed, fixed_info = make_intro(True, plan)
                    offs = bad_tracks()
                for i in sorted(offs):
                    self.log("OGOHLANTIRISH: kinodagi audio#%d (%s) ning kodlash konfiguratsiyasini reklama uchun aynan "
                             "takrorlab bo'lmaydi. Kino ovozi o'zgarishsiz, o'z holicha saqlanadi, lekin reklama davomida "
                             "bu trekda ovoz bo'lmaydi (boshqa treklarda bor)." % (i, audio_label(ma[i])))
                if ma and len(offs) == len(ma):
                    self.log("OGOHLANTIRISH: reklama hech bir audio trekda eshitilmaydi.")

                # ---- vaqt asoslari (timebase) tekshiruvi ----
                use_intro, use_movie, lo = fixed, movie_path, 10
                mism = timebase_mismatch(movie, fixed_info, offs)
                inband = (movie["video"].get("codec_name") in INBAND_BSF) and not video_params_same(movie, fixed_info)
                if mism or inband:
                    if mism:
                        self.vlog("Vaqt asoslari (timebase) mos emas: " + "; ".join(mism))
                    if inband:
                        self.vlog("Kino video parametrlari (SPS/PPS) reklamanikidan farq qiladi: kinoning o'z parametrlari "
                                  "kadrlar ichiga ko'chiriladi (kadr ma'lumoti o'zgarmaydi), shunda kino qotib qolmaydi.")
                    if shutil.disk_usage(out_dir).free < 2 * os.path.getsize(movie_path) + (200 << 20):
                        raise RuntimeError("Vaqtinchalik nusxa uchun diskda joy yetarli emas.")
                    # MP4 kino -> MP4 nusxa: DTS (B-kadrlar tartibi) aynan saqlanadi. MKV da DTS saqlanmaydi, hisoblanadi
                    # va B-piramidali videolarda xato chiqadi, shuning uchun MKV faqat zarurat bo'lganda ishlatiladi.
                    mp4_temp = iext == ".mp4" and not mism
                    norm_movie = os.path.join(tmpdir, "movie_av" + (".mp4" if mp4_temp else ".mkv"))
                    extra = []
                    if mp4_temp:
                        extra = mp4_timescale_args(movie)
                        if movie["video"].get("codec_name") == "hevc":
                            extra += ["-tag:v", "hvc1"]
                    self.vlog("Kino parametrlari reklamanikidan farq qiladi: kino nusxasi tayyorlanmoqda (qayta kodlanmaydi)...")
                    self._ffmpeg(build_av_copy_cmd(ffmpeg, movie_path, movie, norm_movie, inband, extra),
                                 movie["duration"], 10, 40)
                    norm_intro = fixed
                    if not mp4_temp and iext != ".mkv":
                        norm_intro = os.path.join(tmpdir, "intro_av.mkv")
                        self._ffmpeg(build_av_copy_cmd(ffmpeg, fixed, fixed_info, norm_intro), 0, 40, 40)
                    still = timebase_mismatch(ij_probe(ffprobe, norm_movie), ij_probe(ffprobe, norm_intro), offs)
                    if still:
                        raise RuntimeError("Vaqt asoslarini tenglashtirib bo'lmadi: " + "; ".join(still))
                    use_intro, use_movie, lo = norm_intro, norm_movie, 40
                    fixed_info = ij_probe(ffprobe, norm_intro)
                intro_dur = media_span(ffprobe, use_intro, fixed_info["duration"])

                # ---- birlashtirish (video/audio — copy) ----
                lst = os.path.join(tmpdir, "list.txt")
                with open(lst, "w", encoding="utf-8") as f:
                    f.write("file '%s'\n" % concat_escape(os.path.abspath(use_intro)))
                    f.write("duration %.6f\n" % intro_dur)
                    f.write("file '%s'\n" % concat_escape(os.path.abspath(use_movie)))

                keep, skipped = plan_subs(movie["subs"], ext)
                if skipped:
                    kinds = {}
                    for c in skipped:
                        kinds[c] = kinds.get(c, 0) + 1
                    self.log("OGOHLANTIRISH: %s ga sig'magan %d ta subtitr o'tkazib yuborildi (%s). "
                             "Hammasini saqlash uchun natijani .mkv qilib tanlang."
                             % (ext, len(skipped), ", ".join("%s x%d" % kv for kv in kinds.items())))

                is_mkv = ext == ".mkv"
                attach = movie["attach"] if is_mkv else []                 # shrift ilovalari
                chapters = movie["chapters"] if (is_mkv or ext in MP4_EXTS) else []
                cmd = [ffmpeg] + BASE + ["-f", "concat", "-safe", "0", "-i", lst]
                n_in = 1
                if keep or offs or attach:
                    # kinoning o'zidan: subtitrlar, ilovalar va (mos kelmagan) audio treklar, reklama uzunligiga siljitilgan holda
                    cmd += ["-itsoffset", "%.6f" % intro_dur, "-i", movie_path]
                    n_in += 1
                ch_idx = None
                if chapters:
                    chfile = os.path.join(tmpdir, "chapters.ffmeta")
                    with open(chfile, "w", encoding="utf-8") as f:
                        # boblar ham reklama uzunligiga (va muxer siljishiga) mos suriladi
                        f.write(ffmetadata_chapters(chapters, intro_dur + negative_lead(ffprobe, use_intro)))
                    cmd += ["-i", chfile]
                    ch_idx = n_in
                cmd += ["-map", "0:v:0"]
                for i, a in enumerate(ma):
                    cmd += ["-map", ("1:%d" % a["index"]) if i in offs else ("0:a:%d" % i)]
                for st, _ in keep:
                    cmd += ["-map", "1:%d" % st["index"]]
                for at in attach:
                    cmd += ["-map", "1:%d" % at["index"]]
                cmd += ["-c:v", "copy", "-c:a", "copy"] + (["-c:t", "copy"] if attach else [])
                for n, (_, codec) in enumerate(keep):
                    cmd += ["-c:s:%d" % n, codec]
                cmd += ["-map_chapters", str(ch_idx) if ch_idx is not None else "-1"]

                # kinoning til/nom/default ma'lumotlari saqlanadi (-map_metadata -1 ISHLATILMAYDI: u subtitr nomlarini ham o'chirib yuboradi)
                streams = ([(movie["video"], "v:0")] + [(a, "a:%d" % i) for i, a in enumerate(ma)]
                           + [(st, "s:%d" % n) for n, (st, _) in enumerate(keep)])
                if is_mkv:
                    for k, v in copy_tags(movie["tags"]):
                        cmd += ["-metadata", "%s=%s" % (k, v)]
                    for st, spec in streams:
                        for k, v in copy_tags(st):
                            cmd += ["-metadata:s:%s" % spec, "%s=%s" % (k, v)]
                        cmd += ["-disposition:%s" % spec, disp_arg(st)]
                else:
                    title = get_tag(movie["tags"], "title")
                    if title:
                        cmd += ["-metadata", "title=%s" % title]
                    for st, spec in streams:
                        for name in ("language", "title"):
                            val = get_tag(st, name)
                            if val:
                                cmd += ["-metadata:s:%s" % spec, "%s=%s" % (name, val)]
                        if ext in MP4_EXTS and get_tag(st, "title"):
                            cmd += ["-metadata:s:%s" % spec, "handler_name=%s" % get_tag(st, "title")]
                    if ma:
                        if ext in MP4_EXTS:
                            # MP4 da "default" bo'lmagan audio trek o'chirilgan (disabled) yoziladi va ba'zi pleyerlarda
                            # ovozsiz chiqadi, shuning uchun hamma audio treklar yoqilgan holda yoziladi
                            flags = [True] * len(ma)
                        else:
                            has_default = any(a.get("disposition", {}).get("default") for a in ma)
                            flags = [bool(a.get("disposition", {}).get("default")) if has_default else i == 0
                                     for i, a in enumerate(ma)]
                        for i, is_def in enumerate(flags):
                            cmd += ["-disposition:a:%d" % i, "default" if is_def else "0"]
                if ext in MP4_EXTS:
                    if movie["video"].get("codec_name") == "hevc":
                        cmd += ["-tag:v:0", "hvc1"]
                    cmd += ["-movflags", "+faststart"]
                cmd += ["-avoid_negative_ts", "make_zero", "-max_muxing_queue_size", "9999", part]

                self.log("Birlashtirilmoqda...")
                expected = intro_dur + movie["duration"]
                self._ffmpeg(cmd, expected, lo, 100)

                # ---- natijani tekshirish ----
                self._verify(ffmpeg, ffprobe, part, movie, movie_path, intro_dur, expected, keep,
                             len(chapters), len(attach))

                try:
                    os.replace(part, out_path)
                except OSError as e:
                    raise RuntimeError("Natija faylini yozib bo'lmadi (%s). Fayl boshqa dasturda ochiqmi?" % e)
                part = None
                size = os.path.getsize(out_path) / (1024 * 1024)
                self.log("Tayyor: %s (%.1f MB)" % (out_path, size))
                return ("ok", out_path, size)
            except IJCancelled:
                self.log("Bekor qilindi.")
                return ("stop", "")
            except Exception as e:  # noqa: BLE001
                self.log("XATO: %s" % e)
                return ("fail", str(e))
            finally:
                if part and os.path.exists(part):
                    try:
                        os.remove(part)
                    except OSError:
                        pass
                if tmpdir:
                    shutil.rmtree(tmpdir, ignore_errors=True)

        def _verify(self, ffmpeg, ffprobe, path, movie, movie_path, offset, expected, keep,
                    n_chapters=0, n_attach=0):
            """Tayyor faylni tekshiradi: davomiylik, kino kodeklari o'zgarmaganligi, subtitrlar soni."""
            problems = []
            try:
                out = ij_probe(ffprobe, path)
            except Exception as e:  # noqa: BLE001
                raise RuntimeError("Tayyor fayl ochilmadi: %s" % e)
            if abs(out["duration"] - expected) > max(2.0, expected * 0.01):
                problems.append("davomiylik %.1f s (kutilgan %.1f s)" % (out["duration"], expected))
            if out["video"].get("codec_name") != movie["video"].get("codec_name"):
                problems.append("video kodek o'zgargan")
            oa = [a.get("codec_name") for a in out["audio"]]
            ma = [a.get("codec_name") for a in movie["audio"]]
            if oa != ma:
                problems.append("audio oqimlar farq qiladi: %s != %s" % (oa, ma))
            if len(out["subs"]) != len(keep):
                problems.append("subtitrlar soni %d (kutilgan %d)" % (len(out["subs"]), len(keep)))
            else:
                want = [(get_tag(st, "language") or "und") for st, _ in keep]
                got = [(get_tag(st, "language") or "und") for st in out["subs"]]
                if want != got:
                    problems.append("subtitr tillari saqlanmagan")
            if len(out["chapters"]) != n_chapters:
                problems.append("boblar soni %d (kutilgan %d)" % (len(out["chapters"]), n_chapters))
            if len(out["attach"]) != n_attach:
                problems.append("ilovalar (shriftlar) soni %d (kutilgan %d)" % (len(out["attach"]), n_attach))
            for i, (ma_, oa_) in enumerate(zip(movie["audio"], out["audio"])):
                if not audio_params_match(ma_, oa_):
                    problems.append("audio#%d konfiguratsiyasi kinoniki bilan mos emas (ovoz buzilishi mumkin)" % i)
            if self.ts_warn:
                problems.append("ffmpeg %d ta vaqt belgisi ogohlantirishi berdi" % self.ts_warn)
            if movie["audio"] and movie["duration"] > 4:
                self.vlog("Ovoz tekshirilmoqda (har bir audio trek kino bilan solishtiriladi)...")
                for i, why in audio_sanity(ffmpeg, path, movie_path, offset, movie["duration"], len(movie["audio"])):
                    problems.append("audio#%d (%s) kinoniki bilan bir xil emas: %s" % (i, audio_label(movie["audio"][i]), why))
            # tikuv joyi va kino boshi dekodlanadi: dekoder xatolari = "qotib qolish/buzilish" belgisi
            r = subprocess.run(
                [ffmpeg, "-v", "error", "-nostdin", "-ss", "%.3f" % max(0.0, offset - 2.0), "-t", "14", "-i", path,
                 "-map", "0:v:0", "-f", "null", "-"],
                capture_output=True, text=True, encoding="utf-8", errors="replace", creationflags=NO_WINDOW)
            errs = [l.strip() for l in r.stderr.splitlines()
                    if l.strip() and "Attachment" not in l and "analyzeduration" not in l]
            if errs:
                problems.append("tikuv joyida video dekodlash xatolari (%d ta, masalan: %s)" % (len(errs), errs[0][:100]))
            if problems:
                self.log("OGOHLANTIRISH (natijani tekshirib ko'ring): " + "; ".join(problems))
            else:
                self.log("Tekshiruv: hammasi joyida (davomiylik %.1f s, subtitr: %d ta)" % (out["duration"], len(out["subs"])))

    return IntroWindow


# ----------------------------------------------------------------------------------------
#  YUKLOVCHI: M3U8 (HLS) va oddiy havolalar (parallel, davom ettirish bilan)
# ----------------------------------------------------------------------------------------
import urllib.request
import urllib.parse
import urllib.error
from concurrent.futures import ThreadPoolExecutor

DL_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
         "Chrome/124.0 Safari/537.36")
DL_VIDEO_EXT = (".mp4", ".mkv", ".webm", ".avi", ".mov", ".m4v", ".ts", ".flv", ".mp3", ".m4a", ".aac", ".wav", ".flac")
DL_SETTINGS = os.path.join(os.path.expanduser("~"), ".dublyaj_downloader.json")


class DLCancelled(Exception):
    pass


def dl_headers(text="", extra=None):
    """'Nom: qiymat' qatorlaridan sarlavhalar lug'ati (User-Agent standart qo'yiladi)."""
    h = {"User-Agent": DL_UA, "Accept": "*/*"}
    for ln in (text or "").splitlines():
        if ":" in ln:
            k, v = ln.split(":", 1)
            if k.strip():
                h[k.strip()] = v.strip()
    h.update(extra or {})
    return h


def dl_open(url, headers, timeout=30, rng=None, method=None):
    h = dict(headers)
    if rng:
        h["Range"] = rng
    req = urllib.request.Request(url, headers=h, method=method)
    return urllib.request.urlopen(req, timeout=timeout)


def dl_get(url, headers, timeout=30, tries=4):
    last = None
    for k in range(tries):
        try:
            with dl_open(url, headers, timeout) as r:
                return r.read()
        except Exception as e:                    # noqa
            last = e
            time.sleep(0.6 * (k + 1))
    raise last


def dl_name_from_url(url, idx=1):
    p = urllib.parse.urlparse(url)
    base = urllib.parse.unquote(os.path.basename(p.path.rstrip("/")))
    stem = os.path.splitext(base)[0]
    if not stem or stem.lower() in ("index", "master", "playlist", "chunklist", "manifest", "video", "stream"):
        parent = urllib.parse.unquote(os.path.basename(os.path.dirname(p.path.rstrip("/"))))
        stem = parent if parent and parent.lower() not in ("hls", "video") else "video_%d" % idx
    stem = re.sub(r'[\\/:*?"<>|\r\n\t]+', "_", stem).strip(" ._")
    return stem[:120] or "video_%d" % idx


def dl_kind(url, headers):
    """'hls' | 'direct' | 'page' — havola turini aniqlaydi."""
    u = url.strip()
    if os.path.isfile(u):
        return "hls" if u.lower().endswith((".m3u8", ".m3u")) else "direct_local"
    low = urllib.parse.urlparse(u).path.lower()
    if low.endswith((".m3u8", ".m3u")):
        return "hls"
    if low.endswith(DL_VIDEO_EXT):
        return "direct"
    try:                                          # kontent turini tekshirish
        with dl_open(u, headers, 20, rng="bytes=0-511") as r:
            ct = (r.headers.get("Content-Type") or "").lower()
            head = r.read(512)
        if head.lstrip().startswith(b"#EXTM3U") or "mpegurl" in ct:
            return "hls"
        if ct.startswith(("video/", "audio/")) or "octet-stream" in ct:
            return "direct"
    except Exception:
        pass
    return "page"


# --------------------------------- M3U8 tahlili -----------------------------------------
_ATTR = re.compile(r'([A-Z0-9-]+)=("[^"]*"|[^,]*)')


def m3u8_attrs(s):
    return {k: v.strip('"') for k, v in _ATTR.findall(s)}


def m3u8_parse(text, base):
    """Master yoki media playlistni tahlil qiladi."""
    lines = [l.strip() for l in text.replace("\r", "").split("\n") if l.strip()]
    if not lines or not lines[0].startswith("#EXTM3U"):
        raise ValueError("Bu M3U8 playlist emas (#EXTM3U topilmadi).")
    res = {"master": any(l.startswith("#EXT-X-STREAM-INF") for l in lines), "variants": [], "audios": [],
           "segments": [], "keys": [], "maps": [], "seq": 0, "target": 10, "endlist": False,
           "total": 0.0, "fallback": "", "base": base}
    j = lambda u: urllib.parse.urljoin(base, u)
    pend, dur, key_i, map_i = None, 0.0, -1, -1
    for l in lines:
        if l.startswith("#EXT-X-STREAM-INF:"):
            pend = m3u8_attrs(l.split(":", 1)[1])
        elif l.startswith("#EXT-X-MEDIA:"):
            a = m3u8_attrs(l.split(":", 1)[1])
            if a.get("TYPE") == "AUDIO":
                res["audios"].append({"group": a.get("GROUP-ID", ""), "name": a.get("NAME", ""), "lang": a.get("LANGUAGE", ""),
                                      "default": a.get("DEFAULT") == "YES", "uri": j(a["URI"]) if a.get("URI") else ""})
        elif l.startswith("#EXT-X-MEDIA-SEQUENCE:"):
            res["seq"] = int(l.split(":")[1] or 0)
        elif l.startswith("#EXT-X-TARGETDURATION:"):
            res["target"] = int(float(l.split(":")[1] or 10))
        elif l.startswith("#EXT-X-ENDLIST"):
            res["endlist"] = True
        elif l.startswith("#EXT-X-KEY:"):
            a = m3u8_attrs(l.split(":", 1)[1])
            m = a.get("METHOD", "NONE")
            if m == "NONE":
                key_i = -1
            elif m == "AES-128" and a.get("URI"):
                res["keys"].append({"uri": j(a["URI"]), "iv": a.get("IV", "")})
                key_i = len(res["keys"]) - 1
            else:
                res["fallback"] = "shifrlash turi: " + m
        elif l.startswith("#EXT-X-MAP:"):
            a = m3u8_attrs(l.split(":", 1)[1])
            if a.get("BYTERANGE"):
                res["fallback"] = "BYTERANGE"
            res["maps"].append({"uri": j(a["URI"])})
            map_i = len(res["maps"]) - 1
        elif l.startswith("#EXT-X-BYTERANGE"):
            res["fallback"] = "BYTERANGE"
        elif l.startswith("#EXTINF:"):
            try:
                dur = float(l.split(":")[1].split(",")[0])
            except ValueError:
                dur = 0.0
        elif not l.startswith("#"):
            if pend is not None:
                res_s = pend.get("RESOLUTION", "")
                h = int(res_s.split("x")[1]) if "x" in res_s else 0
                res["variants"].append({"uri": j(l), "bw": int(pend.get("BANDWIDTH", pend.get("AVERAGE-BANDWIDTH", 0)) or 0),
                                        "res": res_s, "h": h, "codecs": pend.get("CODECS", ""), "audio": pend.get("AUDIO", ""),
                                        "fps": pend.get("FRAME-RATE", "")})
                pend = None
            else:
                res["segments"].append({"uri": j(l), "dur": dur, "key": key_i, "map": map_i})
                res["total"] += dur
                dur = 0.0
    return res


def dl_pick_variant(variants, pref):
    """pref: 'best' | 'worst' | '<=720' ..."""
    if not variants:
        return None
    key = lambda v: (v["h"], v["bw"])
    if pref == "worst":
        return min(variants, key=key)
    if pref.startswith("<="):
        lim = int(pref[2:])
        ok = [v for v in variants if 0 < v["h"] <= lim]
        return max(ok, key=key) if ok else min(variants, key=key)
    return max(variants, key=key)


def dl_variant_label(v):
    bits = []
    if v["res"]:
        bits.append(v["res"] + (" @%s" % v["fps"] if v["fps"] else ""))
    if v["bw"]:
        bits.append("%.1f Mbit/s" % (v["bw"] / 1e6))
    if v["codecs"]:
        bits.append(v["codecs"])
    return "  |  ".join(bits) or v["uri"]


def dl_load_playlist(src, headers):
    """URL yoki mahalliy fayldan playlist: (matn, base_url)."""
    if os.path.isfile(src):
        with open(src, "r", encoding="utf-8", errors="replace") as f:
            return f.read(), "file:///" + os.path.abspath(src).replace("\\", "/")
    data = dl_get(src, headers)
    return data.decode("utf-8", "replace"), src


# --------------------------------- HLS yuklash -------------------------------------------
class DLSpeed:
    """Oxirgi soniyalar bo'yicha tezlik hisoblagich."""

    def __init__(self):
        self.lock = threading.Lock()
        self.total = 0
        self.t0 = time.time()
        self.win = collections.deque(maxlen=40)

    def add(self, n):
        with self.lock:
            self.total += n
            self.win.append((time.time(), self.total))

    def rate(self):
        with self.lock:
            if len(self.win) < 2:
                return 0.0
            (t1, b1), (t2, b2) = self.win[0], self.win[-1]
            return (b2 - b1) / (t2 - t1) if t2 > t1 else 0.0


def dl_fmt_speed(bps):
    return "%.1f MB/s" % (bps / 1048576) if bps >= 1048576 else "%.0f KB/s" % (bps / 1024)


def hls_fetch_segments(pl, headers, tmp, threads, cancel, report, speed):
    """Playlistdagi hamma fayllarni (kalit, init, segmentlar) parallel yuklaydi; mahalliy playlist matnini qaytaradi."""
    os.makedirs(tmp, exist_ok=True)
    jobs = []
    key_names = []
    for i, k in enumerate(pl["keys"]):
        fn = "key_%d.bin" % i
        key_names.append(fn)
        jobs.append((k["uri"], os.path.join(tmp, fn)))
    map_names = []
    for i, m in enumerate(pl["maps"]):
        fn = "init_%d%s" % (i, os.path.splitext(urllib.parse.urlparse(m["uri"]).path)[1] or ".mp4")
        map_names.append(fn)
        jobs.append((m["uri"], os.path.join(tmp, fn)))
    seg_names = []
    for i, s in enumerate(pl["segments"]):
        ext = os.path.splitext(urllib.parse.urlparse(s["uri"]).path)[1].lower()
        if not ext or len(ext) > 6:
            ext = ".ts"
        fn = "seg_%06d%s" % (i, ext)
        seg_names.append(fn)
        jobs.append((s["uri"], os.path.join(tmp, fn)))
    total = len(jobs)
    done = [0]
    lock = threading.Lock()

    def work(job):
        url, path = job
        if cancel.is_set():
            raise DLCancelled()
        if os.path.isfile(path) and os.path.getsize(path) > 0:      # davom ettirish
            with lock:
                done[0] += 1
            report(done[0], total)
            return
        last = None
        for k in range(6):
            if cancel.is_set():
                raise DLCancelled()
            try:
                with dl_open(url, headers, 30) as r, open(path + ".part", "wb") as f:
                    while True:
                        b = r.read(65536)
                        if not b:
                            break
                        f.write(b)
                        speed.add(len(b))
                        if cancel.is_set():
                            raise DLCancelled()
                os.replace(path + ".part", path)
                with lock:
                    done[0] += 1
                report(done[0], total)
                return
            except DLCancelled:
                raise
            except Exception as e:                # noqa
                last = e
                time.sleep(min(1.0 * (k + 1), 5))
        raise RuntimeError("Yuklab bo'lmadi: %s (%s)" % (url[-70:], last))

    with ThreadPoolExecutor(max(1, threads)) as ex:
        for f in [ex.submit(work, j_) for j_ in jobs]:
            f.result()
    out = ["#EXTM3U", "#EXT-X-VERSION:7" if pl["maps"] else "#EXT-X-VERSION:3",
           "#EXT-X-TARGETDURATION:%d" % (pl["target"] + 1), "#EXT-X-MEDIA-SEQUENCE:%d" % pl["seq"]]
    cur_k, cur_m = -2, -2
    for i, s in enumerate(pl["segments"]):
        if s["key"] != cur_k:
            cur_k = s["key"]
            if cur_k < 0:
                out.append("#EXT-X-KEY:METHOD=NONE")
            else:
                iv = pl["keys"][cur_k]["iv"]
                out.append('#EXT-X-KEY:METHOD=AES-128,URI="%s"%s' % (key_names[cur_k], ",IV=" + iv if iv else ""))
        if s["map"] != cur_m and s["map"] >= 0:
            cur_m = s["map"]
            out.append('#EXT-X-MAP:URI="%s"' % map_names[cur_m])
        out.append("#EXTINF:%.5f," % max(s["dur"], 0.001))
        out.append(seg_names[i])
    out.append("#EXT-X-ENDLIST")
    p = os.path.join(tmp, "local.m3u8")
    with open(p, "w", encoding="utf-8") as f:
        f.write("\n".join(out) + "\n")
    return p


def dl_http_download(url, dst, headers, threads, cancel, report, speed, log=None):
    """Oddiy havola: Range bilan parallel yuklash, .part + davom ettirish."""
    size, ranges_ok = 0, False
    try:
        with dl_open(url, headers, 25, rng="bytes=0-0") as r:
            cr = r.headers.get("Content-Range", "")
            if r.status == 206 and "/" in cr:
                size, ranges_ok = int(cr.split("/")[-1]), True
            else:
                size = int(r.headers.get("Content-Length", 0) or 0)
    except Exception:
        pass
    part = dst + ".part"
    if not ranges_ok or size <= 0 or threads <= 1:
        if log:
            log("Bitta oqimda yuklanmoqda" + ("" if ranges_ok else " (server bo'laklab yuklashni qo'llamaydi)") + "...")
        have = 0
        mode = "wb"
        hdr = dict(headers)
        if ranges_ok and os.path.isfile(part):
            have = os.path.getsize(part)
            hdr["Range"] = "bytes=%d-" % have
            mode = "ab"
        with urllib.request.urlopen(urllib.request.Request(url, headers=hdr), timeout=30) as r, open(part, mode) as f:
            tot = size or int(r.headers.get("Content-Length", 0) or 0) + have
            got = have
            while True:
                if cancel.is_set():
                    raise DLCancelled()
                b = r.read(262144)
                if not b:
                    break
                f.write(b)
                got += len(b)
                speed.add(len(b))
                report(got, tot or got)
        os.replace(part, dst)
        return
    CH = 4 * 1048576
    n = (size + CH - 1) // CH
    meta = part + ".json"
    donec = set()
    if os.path.isfile(part) and os.path.isfile(meta):
        try:
            d = json.load(open(meta))
            if d.get("size") == size and d.get("ch") == CH:
                donec = set(d.get("done", []))
        except Exception:
            donec = set()
    if not os.path.isfile(part) or not donec:
        with open(part, "wb") as f:
            f.truncate(size)
        donec = set()
    lock = threading.Lock()
    got = [sum(min(CH, size - i * CH) for i in donec)]

    def save_meta():
        try:
            json.dump({"size": size, "ch": CH, "done": sorted(donec)}, open(meta, "w"))
        except OSError:
            pass

    def work(i):
        if i in donec:
            return
        a, b = i * CH, min(size, (i + 1) * CH) - 1
        last = None
        for k in range(6):
            if cancel.is_set():
                raise DLCancelled()
            try:
                with dl_open(url, headers, 30, rng="bytes=%d-%d" % (a, b)) as r, open(part, "r+b") as f:
                    f.seek(a)
                    pos = a
                    while pos <= b:
                        x = r.read(min(65536, b - pos + 1))
                        if not x:
                            raise IOError("uzildi")
                        f.write(x)
                        pos += len(x)
                        speed.add(len(x))
                        if cancel.is_set():
                            raise DLCancelled()
                with lock:
                    donec.add(i)
                    got[0] += b - a + 1
                    if len(donec) % 8 == 0:
                        save_meta()
                report(got[0], size)
                return
            except DLCancelled:
                raise
            except Exception as e:                # noqa
                last = e
                time.sleep(min(1.0 * (k + 1), 5))
        raise RuntimeError("Bo'lak yuklanmadi: %s" % last)

    try:
        with ThreadPoolExecutor(max(1, min(threads, n))) as ex:
            for f in [ex.submit(work, i) for i in range(n)]:
                f.result()
    finally:
        save_meta()
    os.replace(part, dst)
    try:
        os.remove(meta)
    except OSError:
        pass


def dl_load_settings():
    try:
        with open(DL_SETTINGS, encoding="utf-8") as f:
            d = json.load(f)
            return d if isinstance(d, dict) else {}
    except (OSError, ValueError):
        return {}


def dl_save_settings(d):
    try:
        with open(DL_SETTINGS, "w", encoding="utf-8") as f:
            json.dump(d, f, ensure_ascii=False, indent=1)
    except OSError:
        pass


def make_downloader_window(tk, ttk, filedialog, messagebox, T):
    """M3U8 / havola yuklovchi — dastur ichidagi alohida oyna (Toplevel)."""
    from tkinter import simpledialog
    BG, CARD, FG, MUTED, ACC = T["BG"], T["CARD"], T["FG"], T["MUTED"], T["ACC"]
    QUALITY = [("Eng yuqori sifat", "best"), ("1080p gacha", "<=1080"), ("720p gacha", "<=720"),
               ("480p gacha", "<=480"), ("Eng past sifat", "worst")]
    KIND_TXT = {"hls": "M3U8 (HLS)", "direct": "To'g'ridan-to'g'ri", "direct_local": "Fayl", "page": "Sahifa (yt-dlp)"}

    class DownloaderWindow(tk.Toplevel):
        def __init__(self, master):
            super().__init__(master)
            self.title("Yuklovchi — M3U8 va havoladagi videolar")
            self.configure(bg=BG)
            self.geometry("1080x900")
            self.minsize(940, 700)
            try:
                self.iconphoto(False, logo_image(64, self))
            except Exception:
                pass
            self.q = queue.Queue()
            self.cancel = threading.Event()
            self.skip_evt = threading.Event()
            self.proc = None
            self.worker = None
            self.rows = []
            self._next = 1
            self.running = False
            self.speed = DLSpeed()
            cfg = dl_load_settings()
            self.v_out = tk.StringVar(value=cfg.get("out", os.path.join(os.path.expanduser("~"), "Downloads")))
            self.v_threads = tk.IntVar(value=int(cfg.get("threads", 12)))
            self.v_q = tk.StringVar(value=next((a for a, b in QUALITY if b == cfg.get("q", "best")), QUALITY[0][0]))
            self.v_ext = tk.StringVar(value=cfg.get("ext", "mp4"))
            self.v_skip = tk.BooleanVar(value=cfg.get("skip", True))
            self.v_status = tk.StringVar(value="Tayyor")
            self.v_speed = tk.StringVar(value="")
            self.ffmpeg = find_tool("ffmpeg")
            self._build()
            self.protocol("WM_DELETE_WINDOW", self._close)
            self.after(120, self._poll)

        # ------------------------------ interfeys ------------------------------
        def _ib(self, parent, text, icon, cmd, style="TButton", width=None):
            b = ttk.Button(parent, text=" " + text, image=icon_image(icon, 18, "#ffffff" if style != "TButton" else FG, self),
                           compound="left", command=cmd, style=style)
            if width:
                b.configure(width=width)
            return b

        def _build(self):
            pad = {"padx": 6, "pady": 4}
            hd = tk.Frame(self, bg="#23252f")
            hd.pack(fill="x")
            tk.Label(hd, image=logo_image(48, self), bg="#23252f").pack(side="left", padx=(16, 10), pady=10)
            tx = tk.Frame(hd, bg="#23252f")
            tx.pack(side="left", pady=8)
            tk.Label(tx, text="Yuklovchi", bg="#23252f", fg="white", font=("Segoe UI", 16, "bold")).pack(anchor="w")
            tk.Label(tx, text="M3U8 (HLS) playlist, to'g'ridan-to'g'ri havola va video sahifalar — parallel, davom ettirish bilan",
                     bg="#23252f", fg=MUTED, font=("Segoe UI", 9)).pack(anchor="w")
            tk.Frame(self, bg="#3fb97a", height=2).pack(fill="x")

            lf = ttk.LabelFrame(self, text="Havolalar (har qatorda bittadan: .m3u8 yoki video havolasi)")
            lf.pack(fill="x", padx=12, pady=(10, 4))
            lf.columnconfigure(0, weight=1)
            self.t_links = tk.Text(lf, height=4, bg="#14151a", fg=FG, insertbackground=FG, relief="flat", highlightthickness=1, highlightbackground="#3a3d4c", highlightcolor=ACC,
                                   font=("Consolas", 10), padx=8, pady=6, wrap="none")
            self.t_links.grid(row=0, column=0, sticky="ew", padx=6, pady=6)
            bb = ttk.Frame(lf)
            bb.grid(row=0, column=1, sticky="n", padx=6, pady=6)
            self._ib(bb, "Navbatga qo'shish", "plus", self.add_links, "Accent.TButton", 20).pack(pady=2)
            self._ib(bb, "Buferdan qo'yish", "link", self.paste_clip, width=20).pack(pady=2)
            self._ib(bb, ".m3u8 fayl tanlash", "file", self.add_files, width=20).pack(pady=2)

            of = ttk.LabelFrame(self, text="Sozlamalar")
            of.pack(fill="x", padx=12, pady=4)
            of.columnconfigure(1, weight=1)
            ttk.Label(of, text="Saqlash papkasi:").grid(row=0, column=0, sticky="w", **pad)
            ttk.Entry(of, textvariable=self.v_out).grid(row=0, column=1, columnspan=5, sticky="ew", **pad)
            self._ib(of, "Tanlash...", "folder", self.pick_out).grid(row=0, column=6, **pad)
            ttk.Label(of, text="Sifat:").grid(row=1, column=0, sticky="w", **pad)
            ttk.Combobox(of, textvariable=self.v_q, values=[a for a, _ in QUALITY], state="readonly", width=18
                         ).grid(row=1, column=1, sticky="w", **pad)
            ttk.Label(of, text="Format:").grid(row=1, column=2, sticky="e", **pad)
            ttk.Combobox(of, textvariable=self.v_ext, values=["mp4", "mkv"], state="readonly", width=6
                         ).grid(row=1, column=3, sticky="w", **pad)
            ttk.Label(of, text="Oqimlar soni:").grid(row=1, column=4, sticky="e", **pad)
            ttk.Spinbox(of, from_=1, to=32, textvariable=self.v_threads, width=5).grid(row=1, column=5, sticky="w", **pad)
            ttk.Checkbutton(of, text="Fayl bor bo'lsa o'tkazib yuborish", variable=self.v_skip
                            ).grid(row=1, column=6, sticky="w", **pad)
            ttk.Label(of, text="Sarlavhalar (ixtiyoriy):\nReferer, Cookie...").grid(row=2, column=0, sticky="nw", **pad)
            self.t_hdr = tk.Text(of, height=3, bg="#14151a", fg=FG, insertbackground=FG, relief="flat", highlightthickness=1, highlightbackground="#3a3d4c", highlightcolor=ACC,
                                 font=("Consolas", 9), padx=8, pady=4, wrap="none")
            self.t_hdr.grid(row=2, column=1, columnspan=6, sticky="ew", **pad)
            self.t_hdr.insert("1.0", dl_load_settings().get("headers", ""))

            qf = ttk.LabelFrame(self, text="Navbat")
            qf.pack(fill="both", expand=True, padx=12, pady=4)
            qf.columnconfigure(0, weight=1)
            qf.rowconfigure(0, weight=1)
            cols = ("n", "name", "kind", "qual", "state")
            self.tree = ttk.Treeview(qf, columns=cols, show="headings", selectmode="extended", height=7)
            for c, t, w, anc in (("n", "№", 36, "center"), ("name", "Nomi / havola", 430, "w"), ("kind", "Turi", 120, "w"),
                                 ("qual", "Sifat", 150, "w"), ("state", "Holat", 260, "w")):
                self.tree.heading(c, text=t)
                self.tree.column(c, width=w, anchor=anc, stretch=c in ("name", "state"))
            sb = ttk.Scrollbar(qf, command=self.tree.yview)
            self.tree.configure(yscrollcommand=sb.set)
            self.tree.grid(row=0, column=0, sticky="nsew", padx=(6, 0), pady=6)
            sb.grid(row=0, column=1, sticky="ns", pady=6)
            for tg, col in (("ok", "#4ade80"), ("fail", "#f87171"), ("run", "#60a5fa"), ("skip", "#fbbf24")):
                self.tree.tag_configure(tg, foreground=col)
            self.tree.bind("<Delete>", lambda _e: self.remove_sel())
            self.tree.bind("<Double-1>", lambda _e: self.rename_sel())
            rb = ttk.Frame(qf)
            rb.grid(row=0, column=2, sticky="ns", padx=6, pady=6)
            self.qbtns = []
            for text, icon, cmd in (("Sifatni tanlash", "gear", self.choose_quality), ("Nomini o'zgartirish", "file", self.rename_sel),
                                    ("Olib tashlash", "trash", self.remove_sel), ("Tozalash", "queue", self.clear),
                                    ("Yuqoriga", "up", lambda: self.move(-1)), ("Pastga", "down", lambda: self.move(1))):
                b = self._ib(rb, text, icon, cmd, width=20)
                b.pack(pady=2)
                self.qbtns.append(b)

            bar = ttk.Frame(self)
            bar.pack(fill="x", padx=12, pady=(6, 0))
            self.b_start = self._ib(bar, "START", "play", self.start, "Accent.TButton")
            self.b_start.pack(side="left", padx=(0, 6), pady=4)
            self.b_stop = self._ib(bar, "STOP", "stop", self.stop, "Stop.TButton")
            self.b_stop.configure(state="disabled")
            self.b_stop.pack(side="left", padx=6, pady=4)
            self.b_skip = self._ib(bar, "Joriysini o'tkazish", "skip", self.skip_cur)
            self.b_skip.configure(state="disabled")
            self.b_skip.pack(side="left", padx=6, pady=4)
            self._ib(bar, "Papkani ochish", "folder", self.open_out).pack(side="right", padx=6, pady=4)
            self._ib(bar, "yt-dlp o'rnatish", "download", self.install_ytdlp).pack(side="right", padx=6, pady=4)

            self.pb = ttk.Progressbar(self, maximum=100)
            self.pb.pack(fill="x", padx=14, pady=(2, 2))
            self.pb_all = ttk.Progressbar(self, maximum=100)
            self.pb_all.pack(fill="x", padx=14, pady=(0, 2))
            sl = ttk.Frame(self)
            sl.pack(fill="x", padx=14)
            ttk.Label(sl, textvariable=self.v_status).pack(side="left")
            ttk.Label(sl, textvariable=self.v_speed, foreground="#4ade80", font=("Segoe UI", 10, "bold")).pack(side="right")
            ttk.Label(self, text="Log", style="Muted.TLabel").pack(anchor="w", padx=14, pady=(6, 0))
            lg = ttk.Frame(self)
            lg.pack(fill="both", expand=True, padx=14, pady=(2, 12))
            self.txt = tk.Text(lg, height=8, wrap="word", state="disabled", bg="#14151a", fg=FG, relief="flat", highlightthickness=1, highlightbackground="#3a3d4c", highlightcolor=ACC,
                               font=("Consolas", 10), padx=8, pady=6)
            s2 = ttk.Scrollbar(lg, command=self.txt.yview)
            self.txt.configure(yscrollcommand=s2.set)
            self.txt.pack(side="left", fill="both", expand=True)
            s2.pack(side="right", fill="y")

        # ------------------------------ navbat ------------------------------
        def log(self, m):
            self.q.put(("log", m))

        def _qpref(self):
            return {a: b for a, b in QUALITY}.get(self.v_q.get(), "best")

        def _add(self, url):
            url = url.strip().strip('"')
            if not url or any(r["url"] == url for r in self.rows):
                return False
            hdr = dl_headers(self.t_hdr.get("1.0", "end"))
            r = {"id": str(self._next), "url": url, "name": dl_name_from_url(url, self._next), "kind": "...", "variant": None,
                 "state": "Kutilmoqda", "tag": "", "out": ""}
            self._next += 1
            self.rows.append(r)
            self.tree.insert("", "end", iid=r["id"], values=(len(self.rows), r["name"], "...", "", "Kutilmoqda"))
            threading.Thread(target=self._sniff, args=(r, hdr), daemon=True).start()
            return True

        def _sniff(self, r, hdr):
            r["kind"] = dl_kind(r["url"], hdr)
            self.q.put(("cell", r["id"], "kind", KIND_TXT.get(r["kind"], r["kind"])))

        def add_links(self):
            n = sum(1 for ln in self.t_links.get("1.0", "end").splitlines() if self._add(ln))
            self.t_links.delete("1.0", "end")
            self._renumber()
            self.log("Navbatga %d ta havola qo'shildi." % n)

        def paste_clip(self):
            try:
                self.t_links.insert("end", self.clipboard_get().strip() + "\n")
            except tk.TclError:
                pass

        def add_files(self):
            ps = filedialog.askopenfilenames(title="M3U8 fayl(lar)ni tanlang",
                                             filetypes=[("Playlist", "*.m3u8 *.m3u"), ("Barcha fayllar", "*.*")])
            for p in ps:
                self._add(p)
            self._renumber()

        def _renumber(self):
            for i, r in enumerate(self.rows, 1):
                if self.tree.exists(r["id"]):
                    self.tree.set(r["id"], "n", i)

        def _sel_rows(self):
            ids = set(self.tree.selection())
            return [r for r in self.rows if r["id"] in ids]

        def remove_sel(self):
            if self.running:
                return
            for r in self._sel_rows():
                self.rows.remove(r)
                self.tree.delete(r["id"])
            self._renumber()

        def clear(self):
            if self.running:
                return
            self.rows.clear()
            self.tree.delete(*self.tree.get_children())

        def move(self, d):
            if self.running:
                return
            sel = self._sel_rows()
            for r in (sel if d < 0 else reversed(sel)):
                i = self.rows.index(r)
                j = i + d
                if 0 <= j < len(self.rows):
                    self.rows[i], self.rows[j] = self.rows[j], self.rows[i]
                    self.tree.move(r["id"], "", j)
            self._renumber()

        def rename_sel(self):
            sel = self._sel_rows()
            if not sel or self.running:
                return
            r = sel[0]
            nm = simpledialog.askstring("Nomini o'zgartirish", "Fayl nomi (kengaytmasiz):", initialvalue=r["name"], parent=self)
            if nm and nm.strip():
                r["name"] = re.sub(r'[\\\\/:*?"<>|]+', "_", nm.strip())
                self.tree.set(r["id"], "name", r["name"])

        def choose_quality(self):
            sel = self._sel_rows()
            if not sel:
                messagebox.showinfo("Sifat", "Avval navbatdan M3U8 qatorini tanlang.", parent=self)
                return
            r = sel[0]
            hdr = dl_headers(self.t_hdr.get("1.0", "end"))
            try:
                text, base = dl_load_playlist(r["url"], hdr)
                pl = m3u8_parse(text, base)
            except Exception as e:                # noqa
                messagebox.showerror("Sifat", "Playlist o'qilmadi:\n%s" % e, parent=self)
                return
            if not pl["master"] or not pl["variants"]:
                messagebox.showinfo("Sifat", "Bu playlistda sifat tanlovi yo'q (bitta oqim).", parent=self)
                return
            vs = sorted(pl["variants"], key=lambda v: (v["h"], v["bw"]), reverse=True)
            dlg = tk.Toplevel(self)
            dlg.title("Sifatni tanlang")
            dlg.configure(bg=BG)
            dlg.transient(self)
            dlg.grab_set()
            lb = tk.Listbox(dlg, width=70, height=min(12, len(vs)), bg=CARD, fg=FG, selectbackground=ACC, relief="flat",
                            font=("Consolas", 10), activestyle="none")
            for v in vs:
                lb.insert("end", dl_variant_label(v))
            lb.selection_set(0)
            lb.pack(padx=12, pady=12)

            def ok():
                i = lb.curselection()
                if i:
                    r["variant"] = vs[i[0]]
                    self.tree.set(r["id"], "qual", r["variant"]["res"] or "tanlangan")
                dlg.destroy()
            ttk.Button(dlg, text="Tanlash", style="Accent.TButton", command=ok).pack(pady=(0, 12))

        def pick_out(self):
            d = filedialog.askdirectory(title="Saqlash papkasi", initialdir=self.v_out.get() or None)
            if d:
                self.v_out.set(d)

        def open_out(self):
            p = self.v_out.get()
            try:
                os.makedirs(p, exist_ok=True)
                if os.name == "nt":
                    os.startfile(p)               # noqa
                else:
                    subprocess.Popen(["xdg-open", p])
            except Exception:
                pass

        def _ytdlp_cmd(self):
            exe = find_tool("yt-dlp")
            if exe:
                return [exe]
            if not FROZEN and importlib.util.find_spec("yt_dlp") is not None:
                return [sys.executable, "-m", "yt_dlp"]
            return None

        def install_ytdlp(self):
            if self._ytdlp_cmd():
                messagebox.showinfo("yt-dlp", "yt-dlp allaqachon o'rnatilgan.", parent=self)
                return
            self.log("yt-dlp o'rnatilmoqda...")

            def w():
                try:
                    if os.name == "nt" or FROZEN:         # tayyor yt-dlp.exe ni yuklab, dastur yoniga qo'yamiz
                        d = os.path.join(app_dir(), "bin")
                        os.makedirs(d, exist_ok=True)
                        dst = os.path.join(d, "yt-dlp.exe" if os.name == "nt" else "yt-dlp")
                        url = "https://github.com/yt-dlp/yt-dlp/releases/latest/download/" + ("yt-dlp.exe" if os.name == "nt" else "yt-dlp")
                        with urllib.request.urlopen(url, timeout=60) as r, open(dst + ".part", "wb") as f:
                            shutil.copyfileobj(r, f)
                        os.replace(dst + ".part", dst)
                        if os.name != "nt":
                            os.chmod(dst, 0o755)
                        self.log("TAYYOR: yt-dlp o'rnatildi: " + dst)
                        return
                    p = subprocess.run([sys.executable, "-m", "pip", "install", "-U", "yt-dlp"], capture_output=True,
                                       text=True, creationflags=_flags())
                    self.log("TAYYOR: yt-dlp o'rnatildi." if p.returncode == 0 else "XATO: yt-dlp o'rnatilmadi:\n" + p.stderr[-400:])
                except Exception as e:            # noqa
                    self.log("XATO: %s" % e)
            threading.Thread(target=w, daemon=True).start()

        # ------------------------------ ishga tushirish ------------------------------
        def _set_running(self, on):
            self.running = on
            self.b_start.configure(state="disabled" if on else "normal")
            self.b_stop.configure(state="normal" if on else "disabled")
            self.b_skip.configure(state="normal" if on else "disabled")
            for b in self.qbtns:
                b.configure(state="disabled" if on else "normal")

        def _save(self):
            dl_save_settings({"out": self.v_out.get(), "threads": int(self.v_threads.get() or 12),
                              "q": self._qpref(), "ext": self.v_ext.get(), "skip": bool(self.v_skip.get()),
                              "headers": self.t_hdr.get("1.0", "end").strip()})

        def start(self):
            self.add_links()
            todo = [r for r in self.rows if r["tag"] != "ok"]
            if not todo:
                messagebox.showinfo("Yuklovchi", "Navbat bo'sh. Havola qo'shing.", parent=self)
                return
            out = self.v_out.get().strip()
            if not out:
                messagebox.showwarning("Yuklovchi", "Saqlash papkasini tanlang.", parent=self)
                return
            try:
                os.makedirs(out, exist_ok=True)
            except OSError as e:
                messagebox.showerror("Yuklovchi", "Papka yaratilmadi:\n%s" % e, parent=self)
                return
            self._save()
            self.cancel.clear()
            self.skip_evt.clear()
            self._set_running(True)
            cfg = dict(out=out, threads=max(1, min(32, int(self.v_threads.get() or 12))), q=self._qpref(),
                       ext=self.v_ext.get(), skip=bool(self.v_skip.get()),
                       hdr_text=self.t_hdr.get("1.0", "end"))
            self.worker = threading.Thread(target=self._run_all, args=(todo, cfg), daemon=True)
            self.worker.start()

        def stop(self):
            self.cancel.set()
            self._kill()
            self.log("To'xtatilmoqda...")

        def skip_cur(self):
            self.skip_evt.set()
            self.cancel.set()
            self._kill()

        def _kill(self):
            p = self.proc
            if p and p.poll() is None:
                try:
                    p.terminate()
                except OSError:
                    pass

        def _close(self):
            if self.worker and self.worker.is_alive():
                if not messagebox.askyesno("Chiqish", "Yuklash ketmoqda. To'xtatib yopilsinmi?", parent=self):
                    return
                self.stop()
                self.worker.join(timeout=6)
            self._save()
            self.destroy()

        def _poll(self):
            try:
                while True:
                    m = self.q.get_nowait()
                    k = m[0]
                    if k == "log":
                        self.txt.configure(state="normal")
                        self.txt.insert("end", "[%s] %s\n" % (time.strftime("%H:%M:%S"), m[1]))
                        self.txt.see("end")
                        self.txt.configure(state="disabled")
                    elif k == "cell":
                        if self.tree.exists(m[1]):
                            self.tree.set(m[1], m[2], m[3])
                    elif k == "row":
                        _, iid, state, tag = m
                        if self.tree.exists(iid):
                            self.tree.set(iid, "state", state)
                            self.tree.item(iid, tags=(tag,))
                            self.tree.see(iid)
                    elif k == "pb":
                        self.pb["value"] = m[1]
                        if len(m) > 2:
                            self.pb_all["value"] = m[2]
                    elif k == "status":
                        self.v_status.set(m[1])
                        self.v_speed.set(m[2] if len(m) > 2 else "")
                    elif k == "done":
                        self._set_running(False)
                        self.v_status.set(m[1])
                        self.v_speed.set("")
            except queue.Empty:
                pass
            self.after(120, self._poll)

        def _rowset(self, r, state, tag):
            r["state"], r["tag"] = state, tag
            self.q.put(("row", r["id"], state, tag))

        # ------------------------------ ish oqimi ------------------------------
        def _run_all(self, todo, cfg):
            n, ok, bad = len(todo), 0, 0
            hdr = dl_headers(cfg["hdr_text"])
            for i, r in enumerate(todo):
                if self.cancel.is_set() and not self.skip_evt.is_set():
                    break
                self.skip_evt.clear()
                self.cancel.clear()
                self.speed = DLSpeed()
                self.q.put(("status", "[%d/%d] %s" % (i + 1, n, r["name"]), ""))
                self.q.put(("pb", 0, i / n * 100))
                self._rowset(r, "Ishlanmoqda...", "run")
                try:
                    if r["kind"] in ("...", None):
                        r["kind"] = dl_kind(r["url"], hdr)
                        self.q.put(("cell", r["id"], "kind", KIND_TXT.get(r["kind"], r["kind"])))
                    res = self._one(r, cfg, hdr, i, n)
                    if res == "skip":
                        self._rowset(r, "O'tkazildi (fayl bor)", "skip")
                    else:
                        r["out"] = res
                        self._rowset(r, "Tayyor", "ok")
                        ok += 1
                        self.log("TAYYOR: %s" % res)
                except DLCancelled:
                    self._rowset(r, "To'xtatildi", "skip")
                    self.log("To'xtatildi: %s" % r["name"])
                    if not self.skip_evt.is_set():
                        break
                except Exception as e:            # noqa
                    bad += 1
                    self._rowset(r, "Xato: %s" % str(e)[:80], "fail")
                    self.log("XATO [%s]: %s" % (r["name"], e))
                self.q.put(("pb", 100 if r["tag"] == "ok" else 0, (i + 1) / n * 100))
            self.q.put(("done", "Tugadi: %d ta tayyor, %d ta xato" % (ok, bad)))

        def _outfile(self, r, cfg, ext):
            base = os.path.join(cfg["out"], r["name"] + "." + ext)
            if os.path.exists(base):
                if cfg["skip"]:
                    return None
                k = 2
                while os.path.exists(os.path.join(cfg["out"], "%s (%d).%s" % (r["name"], k, ext))):
                    k += 1
                base = os.path.join(cfg["out"], "%s (%d).%s" % (r["name"], k, ext))
            return base

        def _one(self, r, cfg, hdr, i, n):
            kind = r["kind"]
            if kind == "hls":
                return self._hls(r, cfg, hdr, i, n)
            if kind in ("direct", "direct_local"):
                return self._direct(r, cfg, hdr, i, n)
            return self._ytdlp(r, cfg, hdr, i, n)

        def _prog(self, frac, i, n, extra=""):
            frac = max(0.0, min(1.0, frac))
            sp = self.speed.rate()
            self.q.put(("pb", frac * 100, (i + frac) / n * 100))
            self.q.put(("status", "[%d/%d] %s  %.0f%%%s" % (i + 1, n, self.rows_name(i), frac * 100, extra),
                        dl_fmt_speed(sp) if sp else ""))

        def rows_name(self, i):
            return getattr(self, "_cur_name", "")

        # ---- HLS ----
        def _hls(self, r, cfg, hdr, i, n):
            if not self.ffmpeg:
                raise RuntimeError("ffmpeg topilmadi (M3U8 ni birlashtirish uchun kerak).")
            self._cur_name = r["name"]
            out = self._outfile(r, cfg, cfg["ext"])
            if out is None:
                return "skip"
            text, base = dl_load_playlist(r["url"], hdr)
            pl = m3u8_parse(text, base)
            apl = None
            if pl["master"]:
                v = r["variant"] or dl_pick_variant(pl["variants"], cfg["q"])
                if not v:
                    raise RuntimeError("Playlistda oqim topilmadi.")
                self.log("Sifat: " + dl_variant_label(v))
                self.q.put(("cell", r["id"], "qual", v["res"] or "avto"))
                t2, b2 = dl_load_playlist(v["uri"], hdr)
                vpl = m3u8_parse(t2, b2)
                cands = [a for a in pl["audios"] if a["group"] == v["audio"] and a["uri"]]
                if cands:
                    a = next((x for x in cands if x["default"]), cands[0])
                    self.log("Alohida audio: %s %s" % (a["name"], a["lang"]))
                    t3, b3 = dl_load_playlist(a["uri"], hdr)
                    apl = m3u8_parse(t3, b3)
            else:
                vpl = pl
            if not vpl["segments"]:
                raise RuntimeError("Playlistda segmentlar yo'q.")
            if not vpl["endlist"]:
                self.log("Diqqat: bu jonli efir playlisti — hozirgi mavjud qismi yuklanadi.")
            if vpl["fallback"] or (apl and apl["fallback"]):
                self.log("Oddiy usul (ffmpeg to'g'ridan-to'g'ri): " + (vpl["fallback"] or apl["fallback"]))
                return self._ffmpeg_direct(r, vpl, out, hdr, i, n, cfg)
            tmp = os.path.join(cfg["out"], ".tmp_" + re.sub(r"\W+", "_", r["name"])[:40])
            self.log("Yuklanmoqda: %d ta segment, %d oqim..." % (len(vpl["segments"]) + (len(apl["segments"]) if apl else 0),
                                                              cfg["threads"]))
            share = 0.9
            wv = len(vpl["segments"]) / max(1, len(vpl["segments"]) + (len(apl["segments"]) if apl else 0))

            def rep_v(d, t):
                self._prog(share * wv * d / t, i, n, "  (%d/%d segment)" % (d, t))

            def rep_a(d, t):
                self._prog(share * (wv + (1 - wv) * d / t), i, n, "  (audio %d/%d)" % (d, t))
            lv = hls_fetch_segments(vpl, hdr, os.path.join(tmp, "v"), cfg["threads"], self.cancel, rep_v, self.speed)
            la = hls_fetch_segments(apl, hdr, os.path.join(tmp, "a"), cfg["threads"], self.cancel, rep_a, self.speed) if apl else None
            self._prog(share, i, n, "  (birlashtirilmoqda...)")
            wl = "file,crypto,data"
            cmd = [self.ffmpeg, "-y", "-hide_banner", "-v", "error", "-nostdin", "-allowed_extensions", "ALL",
                   "-protocol_whitelist", wl, "-i", lv]
            if la:
                cmd += ["-allowed_extensions", "ALL", "-protocol_whitelist", wl, "-i", la, "-map", "0:v:0", "-map", "1:a:0"]
            else:
                cmd += ["-map", "0:v?", "-map", "0:a?"]
            cmd += ["-c", "copy"]
            if out.lower().endswith(".mp4"):
                cmd += ["-movflags", "+faststart"]
            cmd += [out]
            self.proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, creationflags=_flags())
            err = self.proc.communicate()[1].decode("utf-8", "replace")
            rc = self.proc.returncode
            self.proc = None
            if self.cancel.is_set():
                raise DLCancelled()
            if rc != 0 or not os.path.isfile(out) or os.path.getsize(out) < 1024:
                if out.lower().endswith(".mp4"):          # MP4 ba'zi kodeklarni qabul qilmaydi -> MKV
                    out2 = out[:-4] + ".mkv"
                    self.log("MP4 ga yozib bo'lmadi, MKV sinab ko'riladi...")
                    cmd2 = [c for c in cmd[:-1] if c not in ("-movflags", "+faststart")] + [out2]
                    p2 = subprocess.run(cmd2, capture_output=True, creationflags=_flags())
                    if p2.returncode == 0 and os.path.isfile(out2):
                        out = out2
                    else:
                        raise RuntimeError("ffmpeg xatosi: " + (p2.stderr or err.encode()).decode("utf-8", "replace")[-300:])
                else:
                    raise RuntimeError("ffmpeg xatosi: " + err[-300:])
            shutil.rmtree(tmp, ignore_errors=True)
            return out

        def _ffmpeg_direct(self, r, pl, out, hdr, i, n, cfg):
            hs = "".join("%s: %s\r\n" % (k, v) for k, v in hdr.items() if k.lower() != "accept")
            src = r["url"] if not os.path.isfile(r["url"]) else r["url"]
            cmd = [self.ffmpeg, "-y", "-hide_banner", "-v", "error", "-nostdin", "-progress", "pipe:1", "-nostats"]
            if not os.path.isfile(src):
                cmd += ["-headers", hs]
            cmd += ["-allowed_extensions", "ALL", "-i", src, "-map", "0:v?", "-map", "0:a?", "-c", "copy", out]
            total = pl["total"] or 0
            self.proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                                         encoding="utf-8", errors="replace", creationflags=_flags())
            tail = collections.deque(maxlen=5)
            for ln in self.proc.stdout:
                ln = ln.strip()
                if ln.startswith("out_time_us=") and total:
                    try:
                        self._prog(int(ln.split("=")[1]) / 1e6 / total, i, n)
                    except ValueError:
                        pass
                elif ln and "=" not in ln:
                    tail.append(ln)
            rc = self.proc.wait()
            self.proc = None
            if self.cancel.is_set():
                raise DLCancelled()
            if rc != 0:
                raise RuntimeError("ffmpeg: " + " ".join(tail)[-250:])
            return out

        # ---- to'g'ridan-to'g'ri ----
        def _direct(self, r, cfg, hdr, i, n):
            self._cur_name = r["name"]
            ext = os.path.splitext(urllib.parse.urlparse(r["url"]).path)[1].lower()
            ext = ext if ext in DL_VIDEO_EXT else ".mp4"
            out = self._outfile(r, cfg, ext.lstrip("."))
            if out is None:
                return "skip"
            if os.path.isfile(r["url"]):
                shutil.copy2(r["url"], out)
                return out
            self.log("Yuklanmoqda (%d oqim)..." % cfg["threads"])
            dl_http_download(r["url"], out, hdr, cfg["threads"], self.cancel,
                             lambda d, t: self._prog(d / max(t, 1), i, n,
                                                     "  (%.0f / %.0f MB)" % (d / 1048576, t / 1048576)),
                             self.speed, self.log)
            return out

        # ---- sahifa havolalari (yt-dlp) ----
        def _ytdlp(self, r, cfg, hdr, i, n):
            ycmd = self._ytdlp_cmd()
            if not ycmd:
                raise RuntimeError("Bu video sahifa havolasi. 'yt-dlp o'rnatish' tugmasini bosing va qayta urining.")
            self._cur_name = r["name"]
            tpl = os.path.join(cfg["out"], "%(title).120B [%(id)s].%(ext)s")
            cmd = ycmd + ["-f", "bv*+ba/b", "--merge-output-format", cfg["ext"], "-o", tpl,
                   "--newline", "--no-colors", "--no-playlist", "-N", str(min(cfg["threads"], 16))]
            if self.ffmpeg:
                cmd += ["--ffmpeg-location", os.path.dirname(self.ffmpeg) or "."]
            for k, v in hdr.items():
                if k.lower() not in ("user-agent", "accept"):
                    cmd += ["--add-header", "%s:%s" % (k, v)]
            cmd.append(r["url"])
            self.proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                                         encoding="utf-8", errors="replace", creationflags=_flags())
            last, dest = "", ""
            for ln in self.proc.stdout:
                ln = ln.strip()
                m = re.search(r"\[download\]\s+([\d.]+)%.*?at\s+(\S+)", ln)
                if m:
                    self._prog(float(m.group(1)) / 100, i, n)
                    self.q.put(("status", "[%d/%d] %s  %s%%" % (i + 1, n, r["name"], m.group(1)), m.group(2)))
                elif ln:
                    last = ln
                    mm = re.search(r'(?:Destination:|Merging formats into ")\s*"?(.+?)"?$', ln)
                    if mm:
                        dest = mm.group(1)
            rc = self.proc.wait()
            self.proc = None
            if self.cancel.is_set():
                raise DLCancelled()
            if rc != 0:
                raise RuntimeError("yt-dlp: " + last[-200:])
            return dest or cfg["out"]

    return DownloaderWindow



# ----------------------------------------------------------------------------------------
#  YANGILASH: tekshirish / yuklash / o'rnatish / qaytarish
# ----------------------------------------------------------------------------------------
UPD_CFG = os.path.join(os.path.expanduser("~"), ".dublyaj_studio", "update.json")


def upd_cfg_load():
    try:
        with open(UPD_CFG, encoding="utf-8") as f:
            d = json.load(f)
            return d if isinstance(d, dict) else {}
    except (OSError, ValueError):
        return {}


def upd_cfg_save(d):
    try:
        os.makedirs(os.path.dirname(UPD_CFG), exist_ok=True)
        with open(UPD_CFG, "w", encoding="utf-8") as f:
            json.dump(d, f, ensure_ascii=False, indent=1)
    except OSError:
        pass


def gh_norm(url):
    """'owner/repo' yoki 'owner/repo@branch' ni 'github:owner/repo[@branch]/version.json' ga aylantiradi."""
    u = (url or "").strip().strip('"')
    m = re.match(r"^(?:https?://github\.com/)?([A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+?)(?:\.git)?(@[\w./-]+)?/?$", u)
    if u.startswith("github:"):
        return u
    if m and not os.path.exists(u) and not u.lower().startswith(("http://", "https://")) or \
       (m and re.match(r"^https?://github\.com/", u)):
        return "github:%s%s/version.json" % (m.group(1), m.group(2) or "")
    return u


def _read_all(r, cb=None):
    total = int(r.headers.get("Content-Length") or 0) if hasattr(r, "headers") else 0
    buf = bytearray()
    while True:
        ch = r.read(65536)
        if not ch:
            break
        buf += ch
        if cb:
            cb(len(buf), total)
    return bytes(buf)


def upd_fetch(url, timeout=25, cb=None):
    """URL, file:// yoki mahalliy fayl yo'li -> bytes."""
    import urllib.request
    u = gh_norm(url)
    if u.startswith("github:"):
        spec = u[7:]
        repo, _, rest = spec.partition("/")
        r2, _, rest = rest.partition("/")
        r2, _, br = r2.partition("@")
        api = "https://api.github.com/repos/%s/%s/contents/%s" % (repo, r2, rest)
        if br:
            api += "?ref=" + br
        h = {"User-Agent": "DublyajStudio-updater", "Accept": "application/vnd.github.raw+json",
             "X-GitHub-Api-Version": "2022-11-28"}
        tok = (upd_cfg_load().get("token") or "").strip()
        if tok:
            h["Authorization"] = "Bearer " + tok
        try:
            with urllib.request.urlopen(urllib.request.Request(api, headers=h), timeout=timeout) as r:
                return _read_all(r, cb)
        except urllib.error.HTTPError as e:
            if e.code in (401, 403, 404):
                raise ValueError("GitHub: kirish rad etildi (%d). Repo nomi, fayl yoki Token noto'g'ri bo'lishi mumkin "
                                 "(private repo uchun Token kerak)." % e.code)
            raise
    if os.path.isfile(u):
        with open(u, "rb") as f:
            return f.read()
    if u.lower().startswith("file:///"):
        with open(u[8:] if os.name == "nt" else u[7:], "rb") as f:
            return f.read()
    req = urllib.request.Request(u, headers={"User-Agent": "DublyajStudio-updater", "Cache-Control": "no-cache"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return _read_all(r, cb)


def upd_check(url, cb=None):
    """Yangilanish manbasini o'qiydi. Manba: version.json (tavsiya) yoki to'g'ridan-to'g'ri dublyaj_studio.py.
    Qaytaradi: {version, notes, sha256, code(bytes), newer(bool)}"""
    import urllib.parse
    import hashlib
    data = upd_fetch(url) if cb is None else upd_fetch(url)
    text = data.decode("utf-8", "replace").lstrip("\ufeff")
    if text.lstrip().startswith("{"):
        m = json.loads(text)
        ver = str(m.get("version", "")).strip()
        if not ver:
            raise ValueError("version.json ichida 'version' yo'q.")
        code_url = m.get("url") or "dublyaj_studio.py"
        url = gh_norm(url)
        if not re.match(r"^[a-z]+://", code_url) and not os.path.isabs(code_url):
            if url.startswith("github:"):
                code_url = url.rsplit("/", 1)[0] + "/" + code_url
            else:
                code_url = urllib.parse.urljoin(url, code_url) if "://" in url else os.path.join(os.path.dirname(url), code_url)
        code = upd_fetch(code_url, cb=cb)
        sha = (m.get("sha256") or "").lower()
        notes = m.get("notes", "")
    else:
        code, sha, notes = data, "", ""
        ver = src_version(text) or ""
    if sha and hashlib.sha256(code).hexdigest() != sha:
        raise ValueError("Fayl nazorat yig'indisi (sha256) mos kelmadi — yuklab olingan fayl buzilgan yoki almashtirilgan.")
    cv = src_version(code.decode("utf-8", "replace"))
    if not cv:
        raise ValueError("Yuklangan faylda APP_VERSION topilmadi — bu dublyaj_studio.py emas.")
    return {"version": cv, "notes": notes, "sha256": sha, "code": code, "newer": vtuple(cv) > vtuple(APP_VERSION)}


def upd_install(code, force=False):
    """Yangi kodni tekshirib (sintaksis + versiya) yangilanish papkasiga yozadi. Qaytaradi: o'rnatilgan versiya."""
    if not code_sig_ok(code):
        raise ValueError("Yangilanish imzosi noto'g'ri yoki yo'q — bu fayl dasturchi tomonidan berilmagan. O'rnatilmadi.")
    text = code.decode("utf-8", "replace").lstrip("\ufeff")
    ver = src_version(text)
    if not ver:
        raise ValueError("APP_VERSION topilmadi — bu dublyaj_studio.py emas.")
    if "def main(" not in text or "run_gui" not in text:
        raise ValueError("Fayl to'liq emas (main / run_gui topilmadi).")
    compile(text, "dublyaj_studio.py", "exec")                 # sintaksis xatosi bo'lsa o'rnatilmaydi
    if not force and vtuple(ver) <= vtuple(APP_VERSION):
        raise ValueError(f"Bu versiya ({ver}) hozirgisidan ({APP_VERSION}) yangi emas.")
    os.makedirs(UPD_DIR, exist_ok=True)
    if os.path.isfile(UPD_FILE):
        try:
            shutil.copy2(UPD_FILE, UPD_FILE + ".prev")
        except OSError:
            pass
    tmp = UPD_FILE + ".new"
    with open(tmp, "wb") as f:
        f.write(code)
    os.replace(tmp, UPD_FILE)
    for x in (UPD_FILE + ".bad", os.path.join(UPD_DIR, "update_error.txt")):
        try:
            os.remove(x)
        except OSError:
            pass
    return ver


def upd_rollback():
    """Yangilangan nusxani o'chiradi -> EXE ichidagi asl dastur qaytadi. True = nimadir o'chirildi."""
    ok = False
    for x in (UPD_FILE, UPD_FILE + ".bad", UPD_FILE + ".new"):
        try:
            os.remove(x)
            ok = True
        except OSError:
            pass
    return ok


def upd_installed_version():
    try:
        with open(UPD_FILE, encoding="utf-8") as f:
            return src_version(f.read())
    except OSError:
        return None


def restart_app():
    """Dasturni qayta ishga tushiradi (yangi nusxa bilan)."""
    cmd = [sys.executable] if FROZEN else [sys.executable, os.path.abspath(sys.argv[0])]
    flags = 0x00000008 if os.name == "nt" else 0                 # DETACHED_PROCESS
    subprocess.Popen(cmd, close_fds=True, creationflags=flags)


def make_update_window(tk, ttk, filedialog, messagebox, T):
    """Yangilash oynasi: bitta tugma, jarayon va log."""
    BG, CARD, FG, MUTED, ACC = T["BG"], T["CARD"], T["FG"], T["MUTED"], T["ACC"]

    class UpdateWindow(tk.Toplevel):
        def __init__(self, master):
            super().__init__(master)
            self.app = master
            self.title("Yangilash")
            self.configure(bg=BG)
            self.geometry("560x470")
            self.minsize(500, 420)
            try:
                self.iconphoto(False, logo_image(64, self))
            except Exception:
                pass
            self.q = queue.Queue()
            self.busy = False
            hd = tk.Frame(self, bg="#23252f")
            hd.pack(fill="x")
            tk.Label(hd, image=logo_image(48, self), bg="#23252f").pack(side="left", padx=(16, 10), pady=10)
            tx = tk.Frame(hd, bg="#23252f")
            tx.pack(side="left", pady=8)
            tk.Label(tx, text="Yangilash", bg="#23252f", fg="white", font=("Segoe UI", 16, "bold")).pack(anchor="w")
            tk.Label(tx, text="Joriy versiya: %s" % APP_VERSION, bg="#23252f", fg=MUTED,
                     font=("Segoe UI", 9)).pack(anchor="w")
            tk.Frame(self, bg="#e0a030", height=2).pack(fill="x")

            top = ttk.Frame(self)
            top.pack(fill="x", padx=16, pady=(16, 6))
            self.btn = ttk.Button(top, text=" Yangilash", image=icon_image("download", 20, "#ffffff", self), compound="left",
                                  style="Accent.TButton", command=self.go)
            self.btn.pack(fill="x", ipady=8)
            self.pb = ttk.Progressbar(self, maximum=1000, mode="determinate")
            self.pb.pack(fill="x", padx=16, pady=(8, 2))
            self.lbl = ttk.Label(self, text="Tayyor", style="Muted.TLabel")
            self.lbl.pack(anchor="w", padx=16)
            lf = ttk.Frame(self)
            lf.pack(fill="both", expand=True, padx=16, pady=(8, 16))
            self.txt = tk.Text(lf, height=8, wrap="word", state="disabled", bg="#14151a", fg=FG, relief="flat",
                               highlightthickness=1, highlightbackground="#3a3d4c", highlightcolor=ACC,
                               font=("Consolas", 10), padx=8, pady=6)
            self.txt.pack(fill="both", expand=True)
            self.after(120, self._poll)
            self._log("Yangilanishni tekshirish uchun 'Yangilash' tugmasini bosing.")

        def _log(self, m):
            self.txt.configure(state="normal")
            self.txt.insert("end", m + "\n")
            self.txt.see("end")
            self.txt.configure(state="disabled")

        def _prog(self, f, text=None):
            self.pb.configure(mode="determinate")
            self.pb["value"] = max(0, min(1, f)) * 1000
            if text:
                self.lbl.configure(text=text)

        def _poll(self):
            try:
                while True:
                    k, *a = self.q.get_nowait()
                    if k == "log":
                        self._log(a[0])
                    elif k == "prog":
                        self._prog(*a)
                    elif k == "end":
                        self.busy = False
                        self.btn.configure(state="normal")
                        if a[0]:
                            self._ask_restart()
            except queue.Empty:
                pass
            if self.winfo_exists():
                self.after(120, self._poll)

        def _ask_cfg(self):
            """Birinchi marta: repo va token so'raladi (bir marta, keyin eslab qolinadi)."""
            from tkinter import simpledialog
            repo = simpledialog.askstring("Yangilash", "GitHub repo (login/repo):", parent=self)
            if not repo:
                return None
            tok = simpledialog.askstring("Yangilash", "Token (private repo uchun; ochiq bo'lsa bo'sh qoldiring):", parent=self, show="*") or ""
            c = upd_cfg_load()
            c.update(url=repo.strip(), token=tok.strip(), auto=True)
            upd_cfg_save(c)
            return c

        def go(self):
            if self.busy:
                return
            cfg = upd_cfg_load()
            if not (cfg.get("url") or "").strip():
                cfg = self._ask_cfg()
                if not cfg:
                    return
            url = cfg["url"].strip()
            self.busy = True
            self.btn.configure(state="disabled")
            self._prog(0.02, "Tekshirilmoqda...")
            self._log("Yangilanish tekshirilmoqda...")
            P = self.q.put

            def w():
                try:
                    P(("prog", 0.1, "Server bilan aloqa..."))
                    def cb(d, t):
                        P(("prog", 0.2 + 0.55 * (d / t if t else 0.5), "Yuklanmoqda..."))
                    r = upd_check(url, cb)
                    if not r["newer"]:
                        P(("log", "Sizda eng so'nggi versiya (%s). Serverda: %s." % (APP_VERSION, r["version"])))
                        P(("prog", 1.0, "Yangilanish kerak emas"))
                        P(("end", False))
                        return
                    P(("log", "Yangi versiya topildi: %s  (hozir %s)" % (r["version"], APP_VERSION)))
                    if r["notes"]:
                        P(("log", "Yangiliklar: " + str(r["notes"])))
                    P(("log", "Hajmi: %.0f KB. Butunlik (sha256) tekshirildi." % (len(r["code"]) / 1024.0)))
                    P(("prog", 0.85, "O'rnatilmoqda..."))
                    v = upd_install(r["code"])
                    P(("log", "TAYYOR: versiya %s o'rnatildi." % v))
                    P(("prog", 1.0, "Tayyor \u2714 — dasturni qayta ishga tushiring"))
                    P(("end", True))
                except Exception as e:                       # noqa
                    P(("log", "XATO: " + str(e)[:300]))
                    P(("prog", 0.0, "Xato"))
                    P(("end", False))
            threading.Thread(target=w, daemon=True).start()

        def _ask_restart(self):
            if messagebox.askyesno("Yangilash", "Yangilanish o'rnatildi.\n\nDastur qayta ishga tushirilsinmi?", parent=self):
                restart_app()
                self.app.destroy()

    return UpdateWindow


# ----------------------------------------------------------------------------------------
#  GUI
# ----------------------------------------------------------------------------------------
def run_gui(on_ready=None):
    import tkinter as tk
    from tkinter import ttk, filedialog, messagebox

    CFG = os.path.join(os.path.expanduser("~"), ".dublyaj_studio_v7.json")
    BG, CARD, FG, MUTED = "#1c1d22", "#272932", "#e8e8ec", "#9a9cab"
    ACC, RED, GREEN = "#4f8cff", "#d9534f", "#3fb97a"
    TH = dict(BG=BG, CARD=CARD, FG=FG, MUTED=MUTED, ACC=ACC)


    class BatchWindow(tk.Toplevel):
        """Alohida oyna: bir nechta kino + dublyajni ketma-ket ishlash (navbat)."""
        AUTO_TXT = "Avto (eng ko'p kanalli)"
        COLS = ("n", "src", "dub", "aud", "dst", "st")

        def __init__(self, app):
            super().__init__(app)
            self.app = app
            self.title(f"{APP_NAME} — Ko'p fayl (navbat)")
            self.geometry("1180x760+60+30")
            self.minsize(980, 620)
            self.configure(bg=BG)
            self.rows = []                      # dict(src, dub, dst, custom, st)
            self.q = queue.Queue()
            self.worker = None
            self.proc = None
            self.stop_req = False
            self.pcache = {}                    # original yo'li -> audio oqimlar ro'yxati (None = o'qilmoqda, [] = xato)
            self.bulk = None                    # hammasiga qo'llangan audio tanlovi
            self.v_aud = tk.StringVar(value=self.AUTO_TXT)
            self.v_out = tk.StringVar()
            self.v_suffix = tk.StringVar(value="_DUBLYAJ")
            self.v_skip = tk.BooleanVar(value=False)
            self.v_cont = tk.BooleanVar(value=True)
            self.v_info = tk.StringVar()
            self._build()
            for v in (self.v_out, self.v_suffix):
                v.trace_add("write", lambda *_: self._refresh_dst())
            self._info()
            self.protocol("WM_DELETE_WINDOW", self._close)
            self.after(100, self._poll)

        # -- interfeys ---------------------------------------------------------------
        def _build(self):
            s = ttk.Style(self)
            s.configure("Treeview", background=CARD, fieldbackground=CARD, foreground=FG, rowheight=27,
                        borderwidth=0)
            s.configure("Treeview.Heading", background="#343746", foreground=FG, font=("Segoe UI", 10, "bold"),
                        relief="flat")
            s.map("Treeview", background=[("selected", ACC)], foreground=[("selected", "white")])
            root = ttk.Frame(self, padding=10)
            root.pack(fill="both", expand=True)
            root.columnconfigure(0, weight=1)
            root.rowconfigure(1, weight=3)
            root.rowconfigure(6, weight=2)

            tb = ttk.Frame(root)
            tb.grid(row=0, column=0, sticky="ew", pady=(0, 6))
            ttk.Button(tb, text="＋ Original fayllar…", command=self._add_src).pack(side="left")
            ttk.Button(tb, text="＋ Dublyaj fayllar…", command=self._add_dub).pack(side="left", padx=6)
            ttk.Button(tb, text="⇄ Avto-juftlash", command=self._autopair).pack(side="left")
            ttk.Label(tb, text="   Audio oqim (hammasiga):").pack(side="left")
            self.cb_aud = ttk.Combobox(tb, textvariable=self.v_aud, state="readonly", width=24,
                                       values=self._bulk_values())
            self.cb_aud.pack(side="left", padx=4)
            self.cb_aud.bind("<<ComboboxSelected>>", lambda e: self._apply_bulk())
            ttk.Button(tb, text="✕ O'chirish", command=self._remove).pack(side="right")
            ttk.Button(tb, text="↓", width=3, command=lambda: self._move(1)).pack(side="right", padx=(0, 6))
            ttk.Button(tb, text="↑", width=3, command=lambda: self._move(-1)).pack(side="right", padx=(0, 4))
            ttk.Button(tb, text="Tozalash", command=self._clear).pack(side="right", padx=6)

            tf = ttk.Frame(root)
            tf.grid(row=1, column=0, sticky="nsew")
            tf.rowconfigure(0, weight=1)
            tf.columnconfigure(0, weight=1)
            self.tv = ttk.Treeview(tf, columns=self.COLS, show="headings", selectmode="extended")
            for c, t, w, a in (("n", "№", 40, "center"), ("src", "Original (kino)", 290, "w"),
                               ("dub", "Dublyaj", 190, "w"), ("aud", "Audio oqim (original)", 250, "w"),
                               ("dst", "Natija fayli", 280, "w"), ("st", "Holat", 110, "w")):
                self.tv.heading(c, text=t)
                self.tv.column(c, width=w, anchor=a, stretch=(c != "n"))
            vs = ttk.Scrollbar(tf, command=self.tv.yview)
            self.tv.configure(yscrollcommand=vs.set)
            self.tv.grid(row=0, column=0, sticky="nsew")
            vs.grid(row=0, column=1, sticky="ns")
            self.tv.bind("<Double-1>", self._dbl)
            self.tv.bind("<Delete>", lambda e: self._remove())
            self.tv.tag_configure("run", foreground="#8db6ff")
            self.tv.tag_configure("ok", foreground=GREEN)
            self.tv.tag_configure("err", foreground="#ff7a75")
            self.tv.tag_configure("skip", foreground="#e5b84b")
            ttk.Label(root, text="Ikki marta bosing: faylni almashtirish yoki audio oqimni tanlash (bir nechta qatorni belgilab ham bo'ladi).",
                      style="Muted.TLabel").grid(row=2, column=0, sticky="w", pady=(3, 6))

            o = ttk.LabelFrame(root, text=" Natija ", padding=6)
            o.grid(row=3, column=0, sticky="ew")
            o.columnconfigure(1, weight=1)
            ttk.Label(o, text="Natija papkasi:").grid(row=0, column=0, sticky="w", pady=2)
            ttk.Entry(o, textvariable=self.v_out).grid(row=0, column=1, sticky="ew", padx=6)
            ttk.Button(o, text="Tanlash…", command=self._pick_out).grid(row=0, column=2)
            ttk.Label(o, text="(bo'sh = har bir original yonida)", style="Muted.TLabel").grid(row=0, column=3, padx=6)
            ttk.Label(o, text="Nom qo'shimchasi:").grid(row=1, column=0, sticky="w", pady=2)
            ttk.Entry(o, textvariable=self.v_suffix, width=18).grid(row=1, column=1, sticky="w", padx=6)
            ttk.Label(o, textvariable=self.v_info, style="Muted.TLabel").grid(row=1, column=2, columnspan=2, sticky="w")
            ck = ttk.Frame(o)
            ck.grid(row=2, column=0, columnspan=4, sticky="w", pady=(2, 0))
            ttk.Checkbutton(ck, text="Xato bo'lsa keyingisiga o'tish", variable=self.v_cont).pack(side="left")
            ttk.Checkbutton(ck, text="Natija fayli mavjud bo'lsa o'tkazib yuborish",
                            variable=self.v_skip).pack(side="left", padx=14)

            bb = ttk.Frame(root)
            bb.grid(row=4, column=0, sticky="ew", pady=(8, 2))
            self.btn_go = ttk.Button(bb, text="▶  NAVBATNI BOSHLASH", style="Accent.TButton", command=self._start)
            self.btn_go.pack(side="left")
            self.btn_stop = ttk.Button(bb, text="■  STOP", style="Stop.TButton", command=self._stop, state="disabled")
            self.btn_stop.pack(side="left", padx=8)
            ttk.Button(bb, text="Papkani ochish", command=self._open_dir).pack(side="right")

            pf = ttk.Frame(root)
            pf.grid(row=5, column=0, sticky="ew", pady=(4, 4))
            pf.columnconfigure(1, weight=1)
            self.lbl_all = ttk.Label(pf, text="Umumiy: 0 / 0")
            self.lbl_all.grid(row=0, column=0, sticky="w")
            self.pb_all = ttk.Progressbar(pf, maximum=1000)
            self.pb_all.grid(row=0, column=1, sticky="ew", padx=8)
            self.lbl_cur = ttk.Label(pf, text="Joriy fayl: —", style="Muted.TLabel")
            self.lbl_cur.grid(row=1, column=0, sticky="w")
            self.pb_cur = ttk.Progressbar(pf, maximum=1000)
            self.pb_cur.grid(row=1, column=1, sticky="ew", padx=8, pady=(3, 0))

            lg = ttk.LabelFrame(root, text=" Log ", padding=4)
            lg.grid(row=6, column=0, sticky="nsew")
            lg.rowconfigure(0, weight=1)
            lg.columnconfigure(0, weight=1)
            self.txt = tk.Text(lg, height=6, bg="#14151a", fg=FG, relief="flat", font=("Consolas", 10),
                               wrap="word", state="disabled")
            sb = ttk.Scrollbar(lg, command=self.txt.yview)
            self.txt.configure(yscrollcommand=sb.set)
            self.txt.grid(row=0, column=0, sticky="nsew")
            sb.grid(row=0, column=1, sticky="ns")
            self.txt.tag_configure("warn", foreground="#e5b84b")
            self.txt.tag_configure("err", foreground="#ff7a75")
            self.txt.tag_configure("ok", foreground=GREEN)

        def _info(self):
            fmt = self.app.v_fmt.get()
            oc = self.app.v_outch.get()
            self.v_info.set(f"Format: {fmt}  |  {oc}  (asosiy oynadagi sozlamalar hamma fayllarga qo'llanadi)")

        def log(self, msg, tag=None):
            self.txt.configure(state="normal")
            self.txt.insert("end", f"[{time.strftime('%H:%M:%S')}] {msg}\n", tag or ())
            self.txt.see("end")
            self.txt.configure(state="disabled")

        # -- jadval ---------------------------------------------------------------------
        def running(self):
            return bool(self.worker and self.worker.is_alive())

        def _dst_for(self, r):
            if not r["src"]:
                return ""
            ext = FORMATS[self.app.v_fmt.get()]["ext"]
            base = os.path.splitext(os.path.basename(r["src"]))[0] + self.v_suffix.get() + ext
            d = self.v_out.get().strip().strip('"') or os.path.dirname(r["src"])
            return os.path.join(d, base)

        def _refresh_dst(self):
            if self.running():
                return
            self._info()
            for r in self.rows:
                if not r["custom"]:
                    r["dst"] = self._dst_for(r)
            self._redraw()

        # -- audio oqimlar ----------------------------------------------------------------
        def _want_probe(self, src):
            if not src or src in self.pcache:
                return
            self.pcache[src] = None
            def work():
                try:
                    a = probe(self.app.ffprobe, src)["audio"]
                except Exception:
                    a = []
                self.q.put(("probed", src, a))
            if self.app.ffprobe:
                threading.Thread(target=work, daemon=True).start()
            else:
                self.pcache[src] = []

        def _auto_idx(self, aud):
            return max(range(len(aud)), key=lambda x: aud[x]["channels"]) if aud else 0

        def _short(self, a):
            e = f" [{a['lang']}]" if a["lang"] else ""
            return f"#{a['rel']} {a['codec'].upper()} {a['channels']}k{e}"

        def _aud_text(self, r):
            a = self.pcache.get(r["src"]) if r["src"] else []
            if r["src"] and a is None:
                return "o'qilmoqda…"
            if not a:
                return "—"
            if r["aud"] is not None and r["aud"] < len(a):
                return self._short(a[r["aud"]])
            return "Avto: " + self._short(a[self._auto_idx(a)])

        def _bulk_values(self):
            vals = [self.AUTO_TXT] + [f"#{k} oqim" for k in range(4)]
            langs = set()
            for r in self.rows:
                for a in (self.pcache.get(r["src"]) or []):
                    if a["lang"]:
                        langs.add(a["lang"].lower())
            return vals + [f"Til: {l}" for l in sorted(langs)]

        def _apply_bulk(self):
            if self._guard():
                return
            v = self.v_aud.get()
            miss = 0
            for r in self.rows:
                a = self.pcache.get(r["src"]) or []
                if v == self.AUTO_TXT or not a:
                    r["aud"] = None
                elif v.startswith("Til: "):
                    c = [i for i, x in enumerate(a) if x["lang"].lower() == v[5:]]
                    if c:
                        r["aud"] = max(c, key=lambda i: a[i]["channels"])
                    else:
                        r["aud"] = None
                        miss += 1
                else:
                    k = int(v[1:].split(" ")[0])
                    if k < len(a):
                        r["aud"] = k
                    else:
                        r["aud"] = None
                        miss += 1
            if miss:
                self.log(f"{miss} ta faylda tanlangan oqim yo'q — ularda avtomatik tanlanadi.", "warn")
            self._redraw()

        def _pick_stream(self, row):
            r = self.rows[row]
            a = self.pcache.get(r["src"])
            if not a:
                messagebox.showinfo(APP_NAME, "Bu faylning audio oqimlari hali o'qilmagan yoki fayl o'qilmadi.", parent=self)
                return
            sel = [int(i) for i in self.tv.selection()] or [row]
            if row not in sel:
                sel = [row]
            dlg = tk.Toplevel(self)
            dlg.title("Audio oqimni tanlash")
            dlg.configure(bg=BG)
            dlg.transient(self)
            dlg.geometry("+%d+%d" % (self.winfo_rootx() + 200, self.winfo_rooty() + 150))
            f = ttk.Frame(dlg, padding=12)
            f.pack(fill="both", expand=True)
            ttk.Label(f, text=os.path.basename(r["src"])).pack(anchor="w")
            ttk.Label(f, text=f"Tanlangan qatorlar soni: {len(sel)} (ularning ichida shu tartib raqamli oqim olinadi)",
                      style="Muted.TLabel").pack(anchor="w", pady=(0, 6))
            vals = [self.AUTO_TXT] + [describe_stream(x) for x in a]
            v = tk.StringVar(value=vals[(r["aud"] + 1) if r["aud"] is not None and r["aud"] < len(a) else 0])
            cb = ttk.Combobox(f, textvariable=v, state="readonly", values=vals, width=70)
            cb.pack(fill="x", pady=4)

            def ok():
                k = vals.index(v.get()) - 1
                for i in sel:
                    aa = self.pcache.get(self.rows[i]["src"]) or []
                    self.rows[i]["aud"] = None if k < 0 or k >= len(aa) else k
                dlg.destroy()
                self._redraw()
            bf = ttk.Frame(f)
            bf.pack(fill="x", pady=(8, 0))
            ttk.Button(bf, text="OK", style="Accent.TButton", command=ok).pack(side="right")
            ttk.Button(bf, text="Bekor", command=dlg.destroy).pack(side="right", padx=6)
            dlg.grab_set()

        def _redraw(self):
            sel = self.tv.selection()
            idx = [self.tv.index(i) for i in sel]
            self.tv.delete(*self.tv.get_children())
            for i, r in enumerate(self.rows):
                b = lambda x: os.path.basename(x) if x else "—"
                tag = {"Ishlanmoqda": "run", "Tayyor ✔": "ok", "Xato": "err", "O'tkazildi": "skip",
                       "Dublyaj yo'q": "skip", "To'xtatildi": "skip"}.get(r["st"].split(" ")[0] if r["st"].endswith("%") else r["st"], "")
                if r["st"].endswith("%"):
                    tag = "run"
                self.tv.insert("", "end", iid=str(i), values=(i + 1, b(r["src"]), b(r["dub"]), self._aud_text(r), b(r["dst"]), r["st"]),
                               tags=(tag,) if tag else ())
            for i in idx:
                if i < len(self.rows):
                    self.tv.selection_add(str(i))

        def _new_row(self, src="", dub="", aud=None):
            r = dict(src=src, dub=dub, dst="", custom=False, st="Kutmoqda", aud=aud)
            self._want_probe(src)
            r["dst"] = self._dst_for(r)
            return r

        def _guard(self):
            if self.running():
                messagebox.showinfo(APP_NAME, "Navbat ishlayotganda ro'yxatni o'zgartirib bo'lmaydi.", parent=self)
                return True
            return False

        MEDIA = [("Media", "*.mkv *.mp4 *.avi *.mov *.ts *.m2ts *.mka *.wav *.flac *.ac3 *.eac3 *.dts *.aac *.m4a *.mp3 *.ogg *.opus"),
                 ("Hammasi", "*.*")]

        def _add_src(self):
            if self._guard():
                return
            ps = filedialog.askopenfilenames(parent=self, title="Original kinolar (bir nechta tanlash mumkin)",
                                             filetypes=self.MEDIA)
            if not ps:
                return
            for p in sorted(ps, key=natural_key):
                self.rows.append(self._new_row(src=p))
            self._autopair(quiet=True)

        def _add_dub(self):
            if self._guard():
                return
            ps = filedialog.askopenfilenames(parent=self, title="Dublyaj fayllari (bir nechta tanlash mumkin)",
                                             filetypes=self.MEDIA)
            if not ps:
                return
            for p in sorted(ps, key=natural_key):
                self.rows.append(self._new_row(dub=p))
            self._autopair(quiet=True)

        def _autopair(self, quiet=False):
            if self._guard():
                return
            origs = [r["src"] for r in self.rows if r["src"]]
            dubs = [r["dub"] for r in self.rows if r["dub"]]
            old = {r["src"]: r["aud"] for r in self.rows if r["src"]}
            pairs, how = auto_pair(origs, dubs)
            self.rows = [self._new_row(o, d, old.get(o)) for o, d in pairs]
            self._redraw()
            miss = sum(1 for o, d in pairs if not (o and d))
            self.log(f"Juftlash ({how}): {len(pairs)} qator" + (f", to'liq emas: {miss}" if miss else ""),
                     "warn" if miss else None)

        def _remove(self):
            if self._guard():
                return
            idx = sorted((int(i) for i in self.tv.selection()), reverse=True)
            for i in idx:
                del self.rows[i]
            self._redraw()

        def _clear(self):
            if self._guard():
                return
            self.rows = []
            self._redraw()

        def _move(self, d):
            if self._guard():
                return
            idx = sorted(int(i) for i in self.tv.selection())
            if not idx:
                return
            if d < 0 and idx[0] == 0 or d > 0 and idx[-1] == len(self.rows) - 1:
                return
            for i in (idx if d < 0 else reversed(idx)):
                self.rows[i + d], self.rows[i] = self.rows[i], self.rows[i + d]
            self._redraw()
            self.tv.selection_set([str(i + d) for i in idx])

        def _dbl(self, e):
            if self._guard():
                return
            row = self.tv.identify_row(e.y)
            col = self.tv.identify_column(e.x)
            if not row:
                return
            r = self.rows[int(row)]
            if col == "#2":
                p = filedialog.askopenfilename(parent=self, title="Original", filetypes=self.MEDIA)
                if p:
                    r["src"], r["aud"] = p, None
                    self._want_probe(p)
                    if not r["custom"]:
                        r["dst"] = self._dst_for(r)
            elif col == "#3":
                p = filedialog.askopenfilename(parent=self, title="Dublyaj", filetypes=self.MEDIA)
                if p:
                    r["dub"] = p
            elif col == "#4":
                self._pick_stream(int(row))
                return
            elif col == "#5":
                ext = FORMATS[self.app.v_fmt.get()]["ext"]
                p = filedialog.asksaveasfilename(parent=self, title="Natija fayli", defaultextension=ext,
                                                 initialfile=os.path.basename(r["dst"]) if r["dst"] else "")
                if p:
                    r["dst"], r["custom"] = p, True
            self._redraw()

        def _pick_out(self):
            d = filedialog.askdirectory(parent=self, title="Natija papkasi")
            if d:
                self.v_out.set(d)

        def _open_dir(self):
            d = self.v_out.get().strip() or (os.path.dirname(self.rows[0]["src"]) if self.rows and self.rows[0]["src"] else os.getcwd())
            try:
                if os.name == "nt":
                    os.startfile(d)
                elif sys.platform == "darwin":
                    subprocess.Popen(["open", d])
                else:
                    subprocess.Popen(["xdg-open", d])
            except Exception:
                pass

        # -- ishga tushirish ------------------------------------------------------------
        def _start(self):
            if self.running():
                return
            if self.app.worker and self.app.worker.is_alive():
                messagebox.showinfo(APP_NAME, "Asosiy oynada ish davom etmoqda. Tugashini kuting.", parent=self)
                return
            if not (self.app.ffmpeg and self.app.ffprobe):
                self.app._need_ffmpeg()
                return
            try:
                base = self.app._settings()
            except ValueError as e:
                messagebox.showerror(APP_NAME, str(e), parent=self)
                return
            todo, bad = [], []
            for i, r in enumerate(self.rows):
                r["st"] = "Kutmoqda"
                if not r["src"] or not os.path.isfile(r["src"]):
                    r["st"] = "Xato"
                    bad.append(f"{i + 1}: original topilmadi")
                elif not r["dub"] or not os.path.isfile(r["dub"]):
                    r["st"] = "Dublyaj yo'q"
                    bad.append(f"{i + 1}: dublyaj yo'q yoki topilmadi")
                elif os.path.abspath(r["dst"]) == os.path.abspath(r["src"]):
                    r["st"] = "Xato"
                    bad.append(f"{i + 1}: natija fayli original bilan bir xil")
                else:
                    todo.append(i)
            self._redraw()
            if not todo:
                messagebox.showwarning(APP_NAME, "Ishlash uchun to'liq (original + dublyaj) qatorlar yo'q.\n\n"
                                       + "\n".join(bad[:10]), parent=self)
                return
            if bad and not messagebox.askyesno(
                    APP_NAME, f"{len(bad)} ta qator to'liq emas va o'tkazib yuboriladi:\n\n" + "\n".join(bad[:8])
                    + f"\n\nQolgan {len(todo)} tasi ishlansinmi?", parent=self):
                return
            if base.test:
                self.log("Eslatma: 'Sinov rejimi' navbatda o'chirilgan (butun fayllar ishlanadi).", "warn")
            if base.keep_ranges.strip():
                self.log("Eslatma: 'Himoya oraliqlari' navbatda qo'llanmaydi (har bir film uchun alohida).", "warn")
            base = replace(base, test=False, keep_ranges="")
            self.app._save_cfg()
            self.stop_req = False
            self.btn_go.configure(state="disabled")
            self.btn_stop.configure(state="normal")
            self.app.btn_start.configure(state="disabled")
            self.pb_all["value"] = 0
            self.pb_cur["value"] = 0
            cont, skip = self.v_cont.get(), self.v_skip.get()
            jobs = [(i, dict(self.rows[i])) for i in todo]
            self.worker = threading.Thread(target=self._work, args=(base, jobs, cont, skip), daemon=True)
            self.worker.start()

        def _work(self, base, jobs, cont, skip):
            P = lambda *a: self.q.put(a)
            total = len(jobs)
            done = fail = skipped = 0
            t_all = time.time()
            for k, (i, r) in enumerate(jobs):
                if self.stop_req:
                    P("row", i, "To'xtatildi")
                    continue
                if skip and os.path.exists(r["dst"]):
                    P("row", i, "O'tkazildi")
                    skipped += 1
                    P("all", k + 1, total, 0.0)
                    P("log", f"[{i + 1}] {os.path.basename(r['dst'])} mavjud — o'tkazib yuborildi", "warn")
                    continue
                P("row", i, "Ishlanmoqda")
                P("cur", k + 1, total, os.path.basename(r["src"]), 0.0)
                P("log", f"━━ [{i + 1}] {os.path.basename(r['src'])}  +  {os.path.basename(r['dub'])}", None)
                try:
                    d = os.path.dirname(r["dst"])
                    if d:
                        os.makedirs(d, exist_ok=True)
                    info = probe(self.app.ffprobe, r["src"])
                    aud = info["audio"]
                    if not aud:
                        raise RuntimeError("Originalda audio oqim topilmadi.")
                    stream = r["aud"] if (r.get("aud") is not None and r["aud"] < len(aud)) else max(
                        range(len(aud)), key=lambda x: aud[x]["channels"])
                    P("log", f"[{i + 1}] Audio oqim: " + describe_stream(aud[stream]), None)
                    st = replace(base, src=r["src"], dub=r["dub"], dst=r["dst"], stream=stream)
                    t0 = time.time()
                    self.proc = Processor(st, self.app.ffmpeg, self.app.ffprobe,
                                          log=lambda m, i=i: P("log", f"[{i + 1}] {m}", None),
                                          progress=lambda f, t, i=i, k=k: P("prog", i, k, total, f, t))
                    ok, msg = self.proc.run()
                except Exception as e:
                    ok, msg = False, str(e)
                if ok:
                    done += 1
                    P("row", i, "Tayyor ✔")
                    P("log", f"[{i + 1}] TAYYOR ({fmt_time(time.time() - t0)}): {r['dst']}", "ok")
                elif self.stop_req or "To'xtat" in msg:
                    P("row", i, "To'xtatildi")
                    P("log", f"[{i + 1}] To'xtatildi", "warn")
                else:
                    fail += 1
                    P("row", i, "Xato")
                    P("log", f"[{i + 1}] XATO: {msg[:600]}", "err")
                    if not cont:
                        self.stop_req = True
                P("all", k + 1, total, 0.0)
            P("end", done, fail, skipped, total, time.time() - t_all)

        def _stop(self):
            if self.running():
                self.stop_req = True
                self.btn_stop.configure(state="disabled")
                self.log("To'xtatilmoqda (joriy fayl to'xtagach navbat tugaydi)...", "warn")
                if self.proc:
                    self.proc.abort()

        def _poll(self):
            try:
                while True:
                    k, *a = self.q.get_nowait()
                    if k == "log":
                        self.log(a[0], a[1])
                    elif k == "row":
                        self.rows[a[0]]["st"] = a[1]
                        self._redraw()
                    elif k == "probed":
                        self.pcache[a[0]] = a[1]
                        self.cb_aud.configure(values=self._bulk_values())
                        if self.v_aud.get() != self.AUTO_TXT and not self.running():
                            self._apply_bulk()
                        else:
                            self._redraw()
                    elif k == "cur":
                        n, tot, name, f = a
                        self.lbl_cur.configure(text=f"Joriy ({n}/{tot}): {name}")
                        self.pb_cur["value"] = 0
                    elif k == "prog":
                        i, kk, tot, f, text = a
                        if f is not None:
                            self.pb_cur["value"] = f * 1000
                            self.pb_all["value"] = (kk + f) / tot * 1000
                            self.lbl_all.configure(text=f"Umumiy: {kk + 1} / {tot}  ({(kk + f) / tot * 100:.0f}%)")
                            self.rows[i]["st"] = f"{f * 100:.0f}%"
                            self.tv.set(str(i), "st", f"{f * 100:.0f}%")
                    elif k == "all":
                        n, tot, _ = a
                        self.pb_all["value"] = n / tot * 1000
                        self.lbl_all.configure(text=f"Umumiy: {n} / {tot}")
                    elif k == "end":
                        done, fail, skipped, total, took = a
                        self.btn_go.configure(state="normal")
                        self.btn_stop.configure(state="disabled")
                        if not (self.app.worker and self.app.worker.is_alive()):
                            self.app.btn_start.configure(state="normal")
                        self.lbl_cur.configure(text="Joriy fayl: —")
                        self.pb_cur["value"] = 0
                        self._redraw()
                        msg = (f"Navbat tugadi: {done} ta tayyor, {fail} ta xato"
                               + (f", {skipped} ta o'tkazildi" if skipped else "")
                               + f"  (jami {fmt_time(took)})")
                        self.log(msg, "ok" if not fail else "warn")
                        self.app.log("[Navbat] " + msg)
                        messagebox.showinfo(APP_NAME, msg, parent=self)
            except queue.Empty:
                pass
            try:
                self.after(100, self._poll)
            except Exception:
                pass

        def _close(self):
            if self.running():
                if not messagebox.askyesno(APP_NAME, "Navbat ishlamoqda. To'xtatib yopilsinmi?", parent=self):
                    return
                self.stop_req = True
                if self.proc:
                    self.proc.abort()
                self.worker.join(timeout=4)
            self.app.btn_start.configure(state="normal")
            self.app.batch = None
            self.destroy()

    class App(tk.Tk):
        def __init__(self):
            super().__init__()
            self.title(f"{APP_NAME} — Vokalni o'chirish va Ducking")
            h = max(700, min(1060, self.winfo_screenheight() - 90))
            self.geometry(f"1060x{h}+20+10")
            self.minsize(940, 640)
            self.configure(bg=BG)
            self.q = queue.Queue()
            self.worker = None
            self.proc = None
            self.streams = []
            self.ffmpeg = find_tool("ffmpeg")
            self.ffprobe = find_tool("ffprobe")
            self._style()
            try:
                self.iconphoto(True, logo_image(64, self))
            except Exception:
                pass
            self.IntroWin = make_intro_window(tk, ttk, filedialog, messagebox, TH)
            self.DlWin = make_downloader_window(tk, ttk, filedialog, messagebox, TH)
            self.UpdWin = make_update_window(tk, ttk, filedialog, messagebox, TH)
            self.tools = {}
            self._vars()
            self._build()
            self._load_cfg()
            self._set_settings_visible(self.v_open.get())
            self.protocol("WM_DELETE_WINDOW", self._close)
            self.after(100, self._poll)
            self.after(1200, self._auto_update_check)
            self.after(240000, self._lic_tick)
            if not (self.ffmpeg and self.ffprobe):
                self.after(400, self._need_ffmpeg)
            else:
                self.log(f"FFmpeg: {self.ffmpeg}")
            self.log(f"Dastur: {sys.executable}" if FROZEN else f"Python: {sys.executable}")
            if importlib.util.find_spec("onnxruntime") is None:
                self.log("Eslatma: onnxruntime topilmadi. 'AI' ni tanlasangiz, dastur uni shu Python'ga "
                         "o'zi o'rnatishni taklif qiladi (kichik, tez). AI modeli birinchi ishlatishda yuklanadi.", "warn")
            self.v_mode.trace_add("write", lambda *a: self._on_mode())

        def _on_mode(self):
            if self.v_mode.get() != "ai":
                return
            importlib.invalidate_caches()
            eng = {v: k for k, v in ENGINE_LABELS.items()}[self.v_engine.get()]
            if FROZEN:                                  # .exe ichida pip yo'q: onnxruntime tayyor keltirilgan
                if eng == "demucs":
                    self.v_engine.set(ENGINE_LABELS["fast"])
                return
            pkg, mod, size = ("demucs", "demucs", "~2 GB") if eng == "demucs" else ("onnxruntime", "onnxruntime", "~15 MB")
            if importlib.util.find_spec(mod) is not None:
                return
            if messagebox.askyesno(APP_NAME, f"{pkg} shu Python'da o'rnatilmagan.\n\nHozir o'rnatilsinmi? "
                                   f"(pip install {pkg}, {size})\n\n" + sys.executable):
                self.v_mode.set("dsp")
                self.btn_start.configure(state="disabled")
                self.log(f"{pkg} o'rnatilmoqda, kuting...")

                def work():
                    try:
                        p = subprocess.Popen([sys.executable, "-m", "pip", "install", pkg],
                                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                             creationflags=_flags())
                        tail = collections.deque(maxlen=6)
                        for line in iter(p.stdout.readline, b""):
                            tail.append(line.decode("utf-8", "replace").rstrip())
                        rc = p.wait()
                    except Exception as e:                     # noqa
                        rc, tail = -1, [str(e)]
                    self.q.put(("demucs", rc, "\n".join(tail), mod))
                threading.Thread(target=work, daemon=True).start()
            else:
                self.v_mode.set("dsp")

        # -- uslub --------------------------------------------------------------------
        def _style(self):
            s = ttk.Style(self)
            s.theme_use("clam")
            s.configure(".", background=BG, foreground=FG, fieldbackground=CARD, bordercolor="#3a3d4c",
                        lightcolor=CARD, darkcolor=CARD, troughcolor="#14151a", font=("Segoe UI", 10))
            s.configure("TLabel", background=BG, foreground=FG)
            s.configure("Muted.TLabel", foreground=MUTED)
            s.configure("TFrame", background=BG)
            s.configure("TLabelframe", background=BG, bordercolor="#3a3d4c")
            s.configure("TLabelframe.Label", background=BG, foreground=ACC, font=("Segoe UI", 10, "bold"))
            s.configure("TButton", background="#343746", foreground=FG, padding=(10, 6), borderwidth=0)
            s.map("TButton", background=[("active", "#464a60"), ("disabled", "#25262e")],
                  foreground=[("disabled", "#6a6c78")])
            s.configure("Accent.TButton", background=ACC, foreground="white", font=("Segoe UI", 11, "bold"),
                        padding=(22, 9))
            s.map("Accent.TButton", background=[("active", "#6aa0ff"), ("disabled", "#2c3f66")])
            s.configure("Vertical.TScrollbar", background="#5a5f7a", troughcolor="#14151a", arrowcolor=FG,
                        bordercolor="#14151a", lightcolor="#5a5f7a", darkcolor="#5a5f7a", gripcount=0)
            s.map("Vertical.TScrollbar", background=[("active", "#7a80a0")])
            s.configure("Sec.TButton", background="#2d3040", foreground=ACC, font=("Segoe UI", 10, "bold"),
                        padding=(10, 7), anchor="w")
            s.map("Sec.TButton", background=[("active", "#3a3e54")])
            s.configure("Stop.TButton", background=RED, foreground="white", font=("Segoe UI", 11, "bold"),
                        padding=(22, 9))
            s.map("Stop.TButton", background=[("active", "#e8706c"), ("disabled", "#5a3433")])
            s.configure("TCheckbutton", background=BG, foreground=FG)
            s.configure("TRadiobutton", background=BG, foreground=FG)
            s.map("TCheckbutton", background=[("active", BG)])
            s.map("TRadiobutton", background=[("active", BG)])
            s.configure("TEntry", fieldbackground=CARD, foreground=FG, insertcolor=FG)
            s.configure("TSpinbox", fieldbackground=CARD, foreground=FG, arrowcolor=FG, insertcolor=FG)
            s.configure("TCombobox", fieldbackground=CARD, foreground=FG, arrowcolor=FG, background="#343746")
            s.map("TCombobox", fieldbackground=[("readonly", CARD)], foreground=[("readonly", FG)])
            s.configure("Horizontal.TScale", background=BG)
            s.configure("Horizontal.TProgressbar", background=ACC, troughcolor="#14151a", thickness=18)
            s.configure("Treeview", background="#181920", fieldbackground="#181920", foreground=FG, rowheight=26,
                        borderwidth=0)
            s.configure("Treeview.Heading", background="#2d3040", foreground=FG, font=("Segoe UI", 10, "bold"),
                        relief="flat", padding=(6, 5))
            s.map("Treeview", background=[("selected", "#2f4a85")], foreground=[("selected", "white")])
            s.map("Treeview.Heading", background=[("active", "#3a3e54")])
            s.configure("Nav.TButton", background="#2d3040", foreground=FG, padding=(12, 8), borderwidth=0,
                        font=("Segoe UI", 10, "bold"))
            s.map("Nav.TButton", background=[("active", "#3f4460")])
            s.configure("Horizontal.TProgressbar", background=ACC, troughcolor="#14151a", thickness=16)
            s.configure("TNotebook", background=BG)
            self.option_add("*TCombobox*Listbox.background", CARD)
            self.option_add("*TCombobox*Listbox.foreground", FG)
            self.option_add("*TCombobox*Listbox.selectBackground", ACC)

        def _vars(self):
            d = Settings()
            self.v_src, self.v_dub, self.v_dst = tk.StringVar(), tk.StringVar(), tk.StringVar()
            self.v_fmt = tk.StringVar(value=d.fmt)
            self.v_stream = tk.StringVar()
            self.v_mode = tk.StringVar(value=d.mode)
            self.v_engine = tk.StringVar(value=ENGINE_LABELS[d.ai_engine])
            if FROZEN and d.ai_engine == "demucs":
                self.v_engine.set(ENGINE_LABELS["fast"])
            self.v_preset = tk.StringVar(value="Standart (tavsiya)")
            self.num = {k: tk.DoubleVar(value=getattr(d, k)) for k in
                        ("vocal_cut", "f_lo", "f_hi", "sharp", "center_cut", "protect", "leak_cancel", "dip_db", "fc_soft_db", "mask_margin", "mask_max_red", "mask_release", "pad_ms", "pad_dip", "bed_keep", "bed_margin", "duck_db", "thr_db", "attack",
                         "release", "hold", "look", "bg_db", "dub_db", "dub_target", "dub_level_up", "side_margin", "side_max_red", "test_start", "test_len")}
            self.v_fc = tk.StringVar(value=FC_LABELS["soft"])
            self.v_keep = tk.StringVar(value="")
            self.v_surr = tk.BooleanVar(value=d.cut_surround)
            self.v_side = tk.BooleanVar(value=d.side_gentle)
            self.v_aiall = tk.BooleanVar(value=d.ai_all)
            self.v_mix = tk.BooleanVar(value=d.mix_dub)
            self.v_outch = tk.StringVar(value=OUTCH_LABELS["auto"])
            self.v_guided = tk.BooleanVar(value=d.guided)
            self.v_auto = tk.BooleanVar(value=d.auto_dub)
            self.v_mask = tk.BooleanVar(value=d.mask_on)
            self.v_open = tk.BooleanVar(value=False)          # "2. Sozlamalar" bo'limi ochiqmi
            self.v_test = tk.BooleanVar(value=d.test)

        # -- yordamchi vidjetlar --------------------------------------------------------
        def _scale(self, parent, row, text, key, lo, hi, unit, step=1.0, col=0, tip=None):
            var = self.num[key]
            ttk.Label(parent, text=text).grid(row=row, column=col * 3, sticky="w", padx=(8, 6), pady=3)
            val = ttk.Label(parent, text="", width=9, anchor="e", style="Muted.TLabel")

            def upd(_=None):
                v = round(var.get() / step) * step
                var.set(v)
                val.configure(text=(f"{v:.2f}" if step < 0.5 else f"{v:.1f}" if step < 1 else f"{v:.0f}") + f" {unit}")

            sc = ttk.Scale(parent, from_=lo, to=hi, variable=var, command=upd, length=190)
            sc.grid(row=row, column=col * 3 + 1, sticky="ew", padx=4)
            val.grid(row=row, column=col * 3 + 2, sticky="e", padx=(0, 8))
            var.trace_add("write", lambda *a: upd())
            upd()

        def _spin(self, parent, row, col, text, key, lo, hi, inc, w=7):
            ttk.Label(parent, text=text).grid(row=row, column=col * 3, sticky="w", padx=(8, 6), pady=3)
            ttk.Spinbox(parent, from_=lo, to=hi, increment=inc, textvariable=self.num[key], width=w
                        ).grid(row=row, column=col * 3 + 1, sticky="w", padx=4)

        # -- interfeys ------------------------------------------------------------------
        def _build(self):
            # tepada qotib turuvchi sarlavha: logotip + asosiy bo'limlar (alohida oynalar)
            hd = tk.Frame(self, bg="#23252f")
            hd.pack(fill="x")
            tk.Label(hd, image=logo_image(52, self), bg="#23252f").pack(side="left", padx=(16, 10), pady=8)
            tx = tk.Frame(hd, bg="#23252f")
            tx.pack(side="left", pady=6)
            tk.Label(tx, text=APP_NAME, bg="#23252f", fg="white", font=("Segoe UI", 17, "bold")).pack(anchor="w")
            tk.Label(tx, text="Dublyaj · Intro · Yuklovchi",
                     bg="#23252f", fg=MUTED, font=("Segoe UI", 9)).pack(anchor="w")
            nav = tk.Frame(hd, bg="#23252f")
            nav.pack(side="right", padx=14)
            self.nav_btns = {}
            for text, icon, cmd in (("Navbat", "queue", self._open_batch),
                                    ("Intro", "merge", self._open_intro),
                                    ("Yuklovchi", "download", self._open_dl),
                                    ("Yangilash", "refresh", self._open_upd),
                                    ("Haqida", "info", self._about)):
                bt = ttk.Button(nav, text=" " + text, image=icon_image(icon, 18, "#ffffff", self), compound="left",
                                style="Nav.TButton", command=cmd)
                bt.pack(side="left", padx=2, pady=14)
                self.nav_btns[text] = bt
            tk.Frame(self, bg=ACC, height=2).pack(fill="x")
            # butun interfeys aylantiriladigan (scroll) oynada: kontent sig'masa o'ng chetda tayoqcha chiqadi
            holder = ttk.Frame(self)
            holder.pack(fill="both", expand=True)
            self.cv = tk.Canvas(holder, bg=BG, highlightthickness=0, bd=0)
            self.vsb = ttk.Scrollbar(holder, orient="vertical", command=self.cv.yview)
            self.cv.configure(yscrollcommand=self.vsb.set)
            self.cv.pack(side="left", fill="both", expand=True)
            root = ttk.Frame(self.cv, padding=12)
            self._cv_win = self.cv.create_window((0, 0), window=root, anchor="nw")
            self._inner = root

            def sync(_=None):
                ch, cw, rh = self.cv.winfo_height(), self.cv.winfo_width(), root.winfo_reqheight()
                need = rh > ch + 1
                if need and not self.vsb.winfo_ismapped():
                    self.vsb.pack(side="right", fill="y", before=self.cv)
                elif not need and self.vsb.winfo_ismapped():
                    self.vsb.pack_forget()
                    self.cv.yview_moveto(0)
                h = max(ch, rh)
                self.cv.itemconfigure(self._cv_win, width=cw, height=h)
                self.cv.configure(scrollregion=(0, 0, cw, h))
            root.bind("<Configure>", sync)
            self.cv.bind("<Configure>", sync)
            self._sync_scroll = sync

            def wheel(e):
                if not self.vsb.winfo_ismapped() or isinstance(e.widget, tk.Text):
                    return
                step = -1 if (getattr(e, "num", 0) == 5 or e.delta < 0) else 1
                self.cv.yview_scroll(-step * 3, "units")
            self.bind_all("<MouseWheel>", wheel)
            self.bind_all("<Button-4>", wheel)
            self.bind_all("<Button-5>", wheel)
            self.bind_class("TCombobox", "<MouseWheel>", lambda e: "break")   # aylantirishda tanlov o'zgarmasin
            self.bind_class("TScale", "<MouseWheel>", lambda e: "break")
            root.columnconfigure(0, weight=1)
            root.rowconfigure(4, weight=1)

            # 1. Fayllar
            f = ttk.LabelFrame(root, text=" 1. Fayllar ", padding=8)
            f.grid(row=0, column=0, sticky="ew")
            f.columnconfigure(1, weight=1)
            ttk.Label(f, text="Original audio / video:").grid(row=0, column=0, sticky="w", pady=3)
            ttk.Entry(f, textvariable=self.v_src).grid(row=0, column=1, sticky="ew", padx=6)
            ttk.Button(f, text="Tanlash...", command=self._pick_src).grid(row=0, column=2)
            ttk.Label(f, text="Audio oqim (til/kanal):").grid(row=1, column=0, sticky="w", pady=3)
            self.cb_stream = ttk.Combobox(f, textvariable=self.v_stream, state="readonly", values=[])
            self.cb_stream.grid(row=1, column=1, columnspan=2, sticky="ew", padx=6)
            ttk.Label(f, text="Dublyaj ovozi (ixtiyoriy):").grid(row=2, column=0, sticky="w", pady=3)
            ttk.Entry(f, textvariable=self.v_dub).grid(row=2, column=1, sticky="ew", padx=6)
            bb = ttk.Frame(f)
            bb.grid(row=2, column=2)
            ttk.Button(bb, text="Tanlash...", command=self._pick_dub).pack(side="left")
            ttk.Button(bb, text="✕", width=3, command=lambda: self.v_dub.set("")).pack(side="left", padx=(4, 0))
            ttk.Label(f, text="Saqlash joyi:").grid(row=3, column=0, sticky="w", pady=3)
            ttk.Entry(f, textvariable=self.v_dst).grid(row=3, column=1, sticky="ew", padx=6)
            ttk.Button(f, text="Saqlash...", command=self._pick_dst).grid(row=3, column=2)
            ttk.Combobox(f, textvariable=self.v_outch, state="readonly", width=24, values=list(OUTCH_LABELS.values())
                         ).grid(row=4, column=2, padx=(6, 0))
            ttk.Label(f, text="Chiqish formati:").grid(row=4, column=0, sticky="w", pady=3)
            cf = ttk.Combobox(f, textvariable=self.v_fmt, state="readonly", values=list(FORMATS))
            cf.grid(row=4, column=1, sticky="ew", padx=6)
            cf.bind("<<ComboboxSelected>>", lambda e: self._fix_ext())

            ttk.Checkbutton(f, text="AVTOMATIK: dublyaj bor joylardagina original ovoz o'chirilsin, "
                                    "dublyaj yo'q joylar o'zgarishsiz qolsin (tavsiya)",
                            variable=self.v_guided).grid(row=5, column=0, columnspan=3, sticky="w", pady=(6, 0))

            # 2. Sozlamalar
            sect = ttk.Frame(root)
            sect.grid(row=3, column=0, sticky="ew", pady=(4, 0))
            sect.columnconfigure(0, weight=1)
            self.btn_sec = ttk.Button(sect, text="", style="Sec.TButton", command=self._toggle_settings)
            self.btn_sec.grid(row=0, column=0, sticky="ew")
            o = ttk.LabelFrame(sect, text=" Sozlamalar ", padding=8)
            o.grid(row=1, column=0, sticky="ew", pady=(4, 0))
            self.sec_body = o
            o.columnconfigure(0, weight=1)
            o.columnconfigure(1, weight=1)

            top = ttk.Frame(o)
            top.grid(row=0, column=0, columnspan=2, sticky="ew")
            ttk.Label(top, text="Tayyor sozlama:").pack(side="left", padx=(8, 6))
            cp = ttk.Combobox(top, textvariable=self.v_preset, state="readonly", values=list(PRESETS), width=28)
            cp.pack(side="left")
            cp.bind("<<ComboboxSelected>>", lambda e: self._apply_preset())
            ttk.Label(top, text="   Usul:").pack(side="left", padx=(18, 6))
            ttk.Radiobutton(top, text="DSP (tez, markazni o'chirish)", variable=self.v_mode,
                            value="dsp").pack(side="left")
            self.rb_ai = ttk.Radiobutton(top, text="AI:", variable=self.v_mode, value="ai")
            self.rb_ai.pack(side="left", padx=(10, 4))
            ce = ttk.Combobox(top, textvariable=self.v_engine, state="readonly", width=26,
                              values=[v for k, v in ENGINE_LABELS.items() if not (FROZEN and k == "demucs")])
            ce.pack(side="left")
            ce.bind("<<ComboboxSelected>>", lambda e: self._on_mode())

            L = ttk.LabelFrame(o, text=" Vokalni o'chirish ", padding=6)
            L.grid(row=1, column=0, sticky="nsew", padx=(0, 4), pady=(6, 0))
            L.columnconfigure(1, weight=1)
            self._scale(L, 0, "Vokal pasaytirish", "vocal_cut", 0, 80, "dB", 1)
            self._scale(L, 1, "Qat'iylik (kichik = kuchliroq)", "sharp", 0.5, 4, "", 0.25)
            self._scale(L, 2, "Effekt himoyasi: o'q, eshik, zarba (0=o'chiq)", "protect", 0, 100, "%", 5)
            self._scale(L, 3, "5.1 markaz kanal (FC)", "center_cut", 0, 80, "dB", 1)
            self._scale(L, 7, "Dublyaj joyida: barcha kanal nutq pasayishi", "dip_db", 0, 30, "dB", 1)
            self._scale(L, 8, "FC dialogi boshqa kanallardan ayirish", "leak_cancel", 0, 100, "%", 5)
            self._scale(L, 9, "FC yumshoq pasayishi", "fc_soft_db", 0, 40, "dB", 1)
            ttk.Checkbutton(L, text="5.1: yon kanallarda yumshoq ishlov (effektlar saqlansin)",
                            variable=self.v_side).grid(row=10, column=0, columnspan=3, sticky="w", padx=8, pady=(6, 0))
            ttk.Checkbutton(L, text="5.1 AI: old va orqa kanallarni ham AI bilan tozalash (orqa fondagi gaplar; sekinroq)",
                            variable=self.v_aiall).grid(row=13, column=0, columnspan=3, sticky="w", padx=8, pady=(6, 0))
            self._scale(L, 11, "  Yon kanal: original dublyajdan past", "side_margin", 0, 30, "dB", 1)
            self._scale(L, 12, "  Yon kanal: eng ko'p pasayish", "side_max_red", 0, 40, "dB", 1)
            ttk.Label(L, text="FC usuli:").grid(row=4, column=0, sticky="w", padx=(8, 6), pady=3)
            cfc = ttk.Combobox(L, textvariable=self.v_fc, state="readonly", values=list(FC_LABELS.values()))
            cfc.grid(row=4, column=1, columnspan=2, sticky="ew", padx=4)
            r = ttk.Frame(L)
            r.grid(row=5, column=0, columnspan=3, sticky="w", pady=2)
            ttk.Label(r, text="Nutq diapazoni:").pack(side="left", padx=(8, 6))
            ttk.Spinbox(r, from_=40, to=1000, increment=10, textvariable=self.num["f_lo"], width=6).pack(side="left")
            ttk.Label(r, text=" – ").pack(side="left")
            ttk.Spinbox(r, from_=2000, to=20000, increment=500, textvariable=self.num["f_hi"], width=7).pack(side="left")
            ttk.Label(r, text=" Hz", style="Muted.TLabel").pack(side="left")
            ttk.Checkbutton(L, text="Surround (SL/SR) kanallarda ham vokalni o'chirish",
                            variable=self.v_surr).grid(row=6, column=0, columnspan=3, sticky="w", padx=8)

            R = ttk.LabelFrame(o, text=" Ducking (dublyaj bor joyda fonni pasaytirish) ", padding=6)
            R.grid(row=1, column=1, sticky="nsew", padx=(4, 0), pady=(6, 0))
            R.columnconfigure(1, weight=1)
            self._scale(R, 0, "Fon pasayishi", "duck_db", 0, 30, "dB", 1)
            self._scale(R, 1, "Dublyaj bo'sag'asi", "thr_db", -80, -20, "dB", 1)
            self._scale(R, 2, "Attack (tushish)", "attack", 5, 300, "ms", 5)
            self._scale(R, 3, "Release (qaytish)", "release", 50, 2000, "ms", 10)
            self._scale(R, 4, "Hold (ushlab turish)", "hold", 0, 1500, "ms", 10)
            self._scale(R, 5, "Oldindan (lookahead)", "look", 0, 300, "ms", 5)
            ttk.Checkbutton(R, text="Professional niqoblash: original dublyaj spektri ostiga tushadi",
                            variable=self.v_mask).grid(row=6, column=0, columnspan=3, sticky="w", padx=8, pady=(8, 0))
            self._scale(R, 7, "Original masofasi (dublyajdan past)", "mask_margin", 6, 40, "dB", 1)
            self._scale(R, 8, "Niqobdan maksimal pasayish", "mask_max_red", 6, 40, "dB", 1)
            self._scale(R, 9, "Niqob so'nishi (qaytish)", "mask_release", 50, 1000, "ms", 10)
            self._scale(R, 10, "Fon/shovqin saqlash (qaytarish)", "bed_keep", 0, 100, "%", 5)
            self._scale(R, 11, "Fon dublyajdan past eshitilsin", "bed_margin", 4, 30, "dB", 1)
            self._scale(R, 12, "Dublyaj atrofi: oldin/keyin ham tozalash", "pad_ms", 0, 3000, "ms", 50)
            self._scale(R, 13, "Shu atrofda nutq pasayishi", "pad_dip", 0, 40, "dB", 1)

            M = ttk.LabelFrame(o, text=" Aralashtirish va sinov ", padding=6)
            M.grid(row=2, column=0, columnspan=2, sticky="ew", pady=(6, 0))
            M.columnconfigure(1, weight=1)
            M.columnconfigure(4, weight=1)
            self._scale(M, 0, "Fon darajasi", "bg_db", -24, 12, "dB", 0.5, col=0)
            self._scale(M, 0, "Dublyaj darajasi", "dub_db", -24, 18, "dB", 0.5, col=1)
            ttk.Checkbutton(M, text="Dublyaj ovozini ustiga qo'shib saqlash (o'chiq bo'lsa — faqat fon)",
                            variable=self.v_mix).grid(row=1, column=0, columnspan=3, sticky="w", padx=8)
            tr = ttk.Frame(M)
            tr.grid(row=1, column=3, columnspan=3, sticky="w")
            ttk.Checkbutton(tr, text="Sinov rejimi:", variable=self.v_test).pack(side="left", padx=(8, 4))
            ttk.Label(tr, text="boshlanishi").pack(side="left")
            ttk.Spinbox(tr, from_=0, to=100000, increment=10, textvariable=self.num["test_start"],
                        width=7).pack(side="left", padx=4)
            ttk.Label(tr, text="s, davomiyligi").pack(side="left")
            ttk.Spinbox(tr, from_=5, to=600, increment=5, textvariable=self.num["test_len"],
                        width=5).pack(side="left", padx=4)
            ttk.Label(tr, text="s", style="Muted.TLabel").pack(side="left")

            ttk.Checkbutton(M, text="Dublyaj balandligini avtomatik moslash",
                            variable=self.v_auto).grid(row=4, column=0, columnspan=3, sticky="w", padx=8, pady=(6, 0))
            self._scale(M, 4, "Nutq maqsad darajasi", "dub_target", -30, -6, "dBFS", 1, col=1)
            self._scale(M, 5, "Past dublyaj joylarini ko'tarish (eng ko'pi)", "dub_level_up", 0, 12, "dB", 1, col=0)
            ttk.Label(M, text="Himoya oraliqlari (asl ovoz saqlanadi, masalan: 12:30-12:45, 1:02:10-1:02:20):"
                      ).grid(row=2, column=0, columnspan=6, sticky="w", padx=8, pady=(6, 0))
            ttk.Entry(M, textvariable=self.v_keep).grid(row=3, column=0, columnspan=6, sticky="ew", padx=8, pady=2)

            # 3. Progress
            p = ttk.Frame(root)
            p.grid(row=2, column=0, sticky="ew", pady=(6, 0))
            p.columnconfigure(0, weight=1)
            self.pb = ttk.Progressbar(p, maximum=1000)
            self.pb.grid(row=0, column=0, sticky="ew")
            self.lbl_pct = ttk.Label(p, text="0%", width=6, anchor="e", font=("Segoe UI", 11, "bold"))
            self.lbl_pct.grid(row=0, column=1, padx=(8, 0))
            self.lbl_stat = ttk.Label(p, text="Tayyor", style="Muted.TLabel")
            self.lbl_stat.grid(row=1, column=0, columnspan=2, sticky="w", pady=(2, 0))

            # 4. Tugmalar
            b = ttk.Frame(root)
            b.grid(row=1, column=0, sticky="ew", pady=(8, 2))
            self.btn_start = ttk.Button(b, text="▶  START", style="Accent.TButton", command=self._start)
            self.btn_start.pack(side="left")
            self.btn_stop = ttk.Button(b, text="■  STOP", style="Stop.TButton", command=self._stop,
                                       state="disabled")
            self.btn_stop.pack(side="left", padx=8)
            self.btn_prev = ttk.Button(b, text="\u25b6  Sinov ko'rish", command=self._preview)
            self.btn_prev.pack(side="left", padx=(8, 0))
            ttk.Button(b, text="Papkani ochish", command=self._open_dir).pack(side="right")
            ttk.Button(b, text="Logni tozalash", command=self._clear_log).pack(side="right", padx=6)
            ttk.Button(b, text="FFmpeg yo'li", command=self._pick_ffmpeg).pack(side="right")

            # 5. Log
            lg = ttk.LabelFrame(root, text=" Log ", padding=4)
            lg.grid(row=4, column=0, sticky="nsew")
            lg.rowconfigure(0, weight=1)
            lg.columnconfigure(0, weight=1)
            self.txt = tk.Text(lg, height=6, bg="#14151a", fg=FG, insertbackground=FG, relief="flat", highlightthickness=1, highlightbackground="#3a3d4c", highlightcolor=ACC,
                               font=("Consolas", 10), wrap="word", state="disabled")
            sb = ttk.Scrollbar(lg, command=self.txt.yview)
            self.txt.configure(yscrollcommand=sb.set)
            self.txt.grid(row=0, column=0, sticky="nsew")
            sb.grid(row=0, column=1, sticky="ns")
            self.txt.tag_configure("warn", foreground="#e5b84b")
            self.txt.tag_configure("err", foreground="#ff7a75")
            self.txt.tag_configure("ok", foreground=GREEN)

        # -- sozlamalar bo'limini yopish / ochish ----------------------------------------
        def _set_settings_visible(self, vis):
            self.v_open.set(bool(vis))
            if hasattr(self, "_sync_scroll"):
                self.after(30, self._sync_scroll)
            if vis:
                self.sec_body.grid()
                self.btn_sec.configure(text="▼   2. Sozlamalar — yopish")
            else:
                self.sec_body.grid_remove()
                self.btn_sec.configure(text="▶   2. Sozlamalar — ochish (vokal, ducking, niqoblash, aralashtirish)")

        def _toggle_settings(self):
            self._set_settings_visible(not self.v_open.get())
            self.update_idletasks()
            need = self.winfo_reqheight()
            if self.v_open.get() and need > self.winfo_height():       # ochilganda oyna sig'masa kattalashtiramiz
                h = min(need, self.winfo_screenheight() - 80)
                self.geometry(f"{self.winfo_width()}x{h}")

        # -- log / progress -------------------------------------------------------------
        def log(self, msg, tag=None):
            if tag is None:
                low = msg.lower()
                tag = "err" if low.startswith("xato") else "warn" if low.startswith("diqqat") else \
                    "ok" if low.startswith("tayyor") else None
            self.txt.configure(state="normal")
            self.txt.insert("end", time.strftime("[%H:%M:%S] ") + msg + "\n", tag or ())
            self.txt.see("end")
            self.txt.configure(state="disabled")

        def _clear_log(self):
            self.txt.configure(state="normal")
            self.txt.delete("1.0", "end")
            self.txt.configure(state="disabled")

        def _poll(self):
            try:
                while True:
                    k, *a = self.q.get_nowait()
                    if k == "log":
                        self.log(a[0])
                    elif k == "prog":
                        frac, text = a
                        if frac is None:
                            self.pb.configure(mode="indeterminate")
                            self.pb.step(10)
                            self.lbl_pct.configure(text="…")
                        else:
                            self.pb.configure(mode="determinate")
                            self.pb["value"] = frac * 1000
                            self.lbl_pct.configure(text=f"{frac * 100:.0f}%")
                        self.lbl_stat.configure(text=text)
                    elif k == "demucs":
                        rc, out, mod = a
                        self.btn_start.configure(state="normal")
                        importlib.invalidate_caches()
                        if rc == 0 and importlib.util.find_spec(mod) is not None:
                            self.log(f"TAYYOR: {mod} o'rnatildi. Endi AI rejimini tanlang.")
                        else:
                            self.log(f"XATO: {mod} o'rnatilmadi:\n" + out)
                    elif k == "done":
                        ok, msg = a
                        self._finish(ok, msg)
                    elif k == "pdone":
                        ok, msg, path = a
                        self._preview_done(ok, msg, path)
            except queue.Empty:
                pass
            self.after(100, self._poll)

        # -- fayl tanlash ---------------------------------------------------------------
        def _pick_src(self):
            p = filedialog.askopenfilename(title="Original audio yoki video", filetypes=[
                ("Media", "*.mkv *.mp4 *.avi *.mov *.ts *.m2ts *.mka *.wav *.flac *.ac3 *.eac3 *.dts *.aac *.m4a *.mp3 *.ogg *.opus"),
                ("Hammasi", "*.*")])
            if p:
                self.v_src.set(p)
                self._probe_src(p)

        def _probe_src(self, p):
            if not self.ffprobe:
                return
            try:
                info = probe(self.ffprobe, p)
            except Exception as e:
                self.log(f"XATO: {e}")
                return
            self.streams = info["audio"]
            vals = [describe_stream(a) for a in self.streams]
            self.cb_stream.configure(values=vals)
            if vals:
                best = max(range(len(self.streams)), key=lambda i: self.streams[i]["channels"])
                self.cb_stream.current(best)
            self.log(f"Fayl: {os.path.basename(p)} — {len(vals)} ta audio oqim, "
                     f"davomiyligi {fmt_time(info['duration'])}")
            ext = FORMATS[self.v_fmt.get()]["ext"]
            self.v_dst.set(os.path.splitext(p)[0] + "_FON" + ext)

        def _pick_dub(self):
            p = filedialog.askopenfilename(title="Dublyaj ovozi (butun film uzunligida)", filetypes=[
                ("Audio", "*.wav *.flac *.mp3 *.aac *.m4a *.ac3 *.eac3 *.ogg *.opus *.mka *.aif *.aiff"),
                ("Hammasi", "*.*")])
            if p:
                self.v_dub.set(p)

        def _pick_dst(self):
            ext = FORMATS[self.v_fmt.get()]["ext"]
            p = filedialog.asksaveasfilename(title="Saqlash joyi", defaultextension=ext,
                                             initialfile=os.path.basename(self.v_dst.get()) or "natija" + ext,
                                             filetypes=[(self.v_fmt.get(), "*" + ext), ("Hammasi", "*.*")])
            if p:
                self.v_dst.set(p)

        def _fix_ext(self):
            d = self.v_dst.get()
            if d:
                self.v_dst.set(os.path.splitext(d)[0] + FORMATS[self.v_fmt.get()]["ext"])

        def _open_dir(self):
            d = os.path.dirname(self.v_dst.get()) or os.getcwd()
            try:
                if os.name == "nt":
                    os.startfile(d)
                elif sys.platform == "darwin":
                    subprocess.Popen(["open", d])
                else:
                    subprocess.Popen(["xdg-open", d])
            except Exception:
                pass

        def _need_ffmpeg(self):
            messagebox.showwarning(APP_NAME, "FFmpeg / FFprobe topilmadi.\n\nffmpeg.exe va ffprobe.exe ni shu "
                                   "skript turgan papkaga qo'ying yoki PATH ga qo'shing,\nyoki 'FFmpeg yo'li' "
                                   "tugmasi bilan ko'rsating.")

        def _pick_ffmpeg(self):
            p = filedialog.askopenfilename(title="ffmpeg ni tanlang (ffprobe shu papkada bo'lishi kerak)")
            if p:
                d = os.path.dirname(p)
                ext = ".exe" if os.name == "nt" else ""
                self.ffmpeg = p
                fp = os.path.join(d, "ffprobe" + ext)
                self.ffprobe = fp if os.path.isfile(fp) else find_tool("ffprobe")
                self.log(f"FFmpeg: {self.ffmpeg} | FFprobe: {self.ffprobe}")

        # -- sozlamalar -----------------------------------------------------------------
        def _apply_preset(self):
            for k, v in PRESETS[self.v_preset.get()].items():
                if k == "fc":
                    self.v_fc.set(FC_LABELS[v])
                elif k == "surr":
                    self.v_surr.set(bool(v))
                elif k == "side":
                    self.v_side.set(bool(v))
                elif k == "ai_all":
                    self.v_aiall.set(bool(v))
                elif k == "mode":
                    self.v_mode.set(v)
                elif k == "ai_engine":
                    self.v_engine.set(ENGINE_LABELS[v])
                elif k == "guided":
                    self.v_guided.set(bool(v))
                elif k == "mask_on":
                    self.v_mask.set(bool(v))
                elif k == "auto_dub":
                    self.v_auto.set(bool(v))
                else:
                    self.num[k].set(v)
            if self.v_mode.get() == "ai":
                self._on_mode()

        def _settings(self):
            n = {}
            for k, v in self.num.items():
                try:
                    n[k] = float(v.get())
                except Exception:
                    raise ValueError(f"'{k}' maydoniga noto'g'ri qiymat kiritilgan.")
            if n["f_lo"] >= n["f_hi"]:
                raise ValueError("Nutq diapazoni: pastki chegara yuqorisidan kichik bo'lishi kerak.")
            st = Settings(src=self.v_src.get().strip().strip('"'), dst=self.v_dst.get().strip().strip('"'),
                          dub=self.v_dub.get().strip().strip('"'),
                          stream=max(self.cb_stream.current(), 0), fmt=self.v_fmt.get(),
                          mode=self.v_mode.get(), ai_engine={v: k for k, v in ENGINE_LABELS.items()}[self.v_engine.get()], cut_surround=self.v_surr.get(), side_gentle=self.v_side.get(), ai_all=self.v_aiall.get(), guided=self.v_guided.get(), auto_dub=self.v_auto.get(), mask_on=self.v_mask.get(),
                          fc_mode={v: k for k, v in FC_LABELS.items()}[self.v_fc.get()],
                          keep_ranges=self.v_keep.get(), mix_dub=self.v_mix.get(),
                          out_ch={v: k for k, v in OUTCH_LABELS.items()}[self.v_outch.get()],
                          test=self.v_test.get(), **n)
            return st

        def _save_cfg(self):
            try:
                data = {k: v.get() for k, v in self.num.items()}
                data.update(open=self.v_open.get(), mask=self.v_mask.get(), auto=self.v_auto.get(), guided=self.v_guided.get(), fc=self.v_fc.get(), keep=self.v_keep.get(), fmt=self.v_fmt.get(), mode=self.v_mode.get(), engine=self.v_engine.get(), surr=self.v_surr.get(), side=self.v_side.get(), aiall=self.v_aiall.get(),
                            mix=self.v_mix.get(), outch=self.v_outch.get(), test=self.v_test.get(), preset=self.v_preset.get())
                with open(CFG, "w", encoding="utf-8") as f:
                    json.dump(data, f)
            except Exception:
                pass

        def _load_cfg(self):
            try:
                with open(CFG, encoding="utf-8") as f:
                    d = json.load(f)
                for k, v in self.num.items():
                    if k in d:
                        v.set(d[k])
                if d.get("fmt") in FORMATS:
                    self.v_fmt.set(d["fmt"])
                self.v_mode.set(d.get("mode", "dsp"))
                if d.get("engine") in ENGINE_LABELS.values():
                    self.v_engine.set(d["engine"])
                if d.get("fc") in FC_LABELS.values():
                    self.v_fc.set(d["fc"])
                if d.get("outch") in OUTCH_LABELS.values():
                    self.v_outch.set(d["outch"])
                self.v_keep.set(d.get("keep", ""))
                self.v_guided.set(d.get("guided", True))
                self.v_auto.set(d.get("auto", True))
                self.v_mask.set(d.get("mask", True))
                self._set_settings_visible(d.get("open", False))
                self.v_surr.set(d.get("surr", False))
                self.v_side.set(d.get("side", False))
                self.v_aiall.set(d.get("aiall", False))
                self.v_mix.set(d.get("mix", True))
                self.v_test.set(d.get("test", False))
                if d.get("preset") in PRESETS:
                    self.v_preset.set(d["preset"])
            except Exception:
                pass

        # -- start / stop -----------------------------------------------------------------
        def _start(self):
            try:
                st = self._settings()
            except ValueError as e:
                messagebox.showerror(APP_NAME, str(e))
                return
            if getattr(self, "batch", None) is not None and self.batch.running():
                messagebox.showinfo(APP_NAME, "Navbat (ko'p fayl) ishlamoqda. Tugashini kuting yoki uni to'xtating.")
                return
            if not (self.ffmpeg and self.ffprobe):
                self._need_ffmpeg()
                return
            if not st.src or not os.path.isfile(st.src):
                messagebox.showerror(APP_NAME, "Original faylni tanlang.")
                return
            if not st.dst:
                messagebox.showerror(APP_NAME, "Saqlash joyini ko'rsating.")
                return
            if os.path.abspath(st.dst) == os.path.abspath(st.src):
                messagebox.showerror(APP_NAME, "Saqlash fayli original bilan bir xil bo'lmasligi kerak.")
                return
            if os.path.exists(st.dst) and not messagebox.askyesno(APP_NAME, "Fayl mavjud. Ustiga yozilsinmi?"):
                return
            if st.mix_dub and not st.dub:
                pass  # dublyaj yo'q: faqat fon
            self._save_cfg()
            self.btn_start.configure(state="disabled")
            self.btn_prev.configure(state="disabled")
            self.btn_stop.configure(state="normal")
            self.pb["value"] = 0
            self.lbl_pct.configure(text="0%")
            self.lbl_stat.configure(text="Boshlanmoqda...")
            self.proc = Processor(st, self.ffmpeg, self.ffprobe,
                                  log=lambda m: self.q.put(("log", m)),
                                  progress=lambda f, t: self.q.put(("prog", f, t)))
            self.worker = threading.Thread(target=lambda: self.q.put(("done",) + self.proc.run()), daemon=True)
            self.worker.start()

        def _preview(self):
            """Sinov: kinoning qisqa qismini hozirgi sozlamalar bilan ishlab, video + natija/original audio yo'li bilan ochadi."""
            try:
                st = self._settings()
            except ValueError as e:
                messagebox.showerror(APP_NAME, str(e))
                return
            if getattr(self, "batch", None) is not None and self.batch.running():
                messagebox.showinfo(APP_NAME, "Navbat ishlamoqda. Tugashini kuting.")
                return
            if not (self.ffmpeg and self.ffprobe):
                self._need_ffmpeg()
                return
            if not st.src or not os.path.isfile(st.src):
                messagebox.showerror(APP_NAME, "Avval original faylni tanlang.")
                return
            import tempfile
            tdir = os.path.join(tempfile.gettempdir(), "dublyaj_preview")
            os.makedirs(tdir, exist_ok=True)
            wav = os.path.join(tdir, "natija.wav")
            out = os.path.join(tdir, "sinov_video.mkv")
            for x in (wav, out):
                try:
                    os.remove(x)
                except OSError:
                    pass
            st = replace(st, test=True, dst=wav, fmt="WAV 24-bit (PCM)")
            self._save_cfg()
            self.btn_start.configure(state="disabled")
            self.btn_prev.configure(state="disabled")
            self.btn_stop.configure(state="normal")
            self.pb["value"] = 0
            self.lbl_pct.configure(text="0%")
            self.lbl_stat.configure(text="Sinov tayyorlanmoqda...")
            self.log("=== SINOV: %s dan %s davomida (hozirgi sozlamalar bilan) ===" % (fmt_time(st.test_start), fmt_time(st.test_len)))
            self.proc = Processor(st, self.ffmpeg, self.ffprobe,
                                  log=lambda m: self.q.put(("log", m)),
                                  progress=lambda f, t: self.q.put(("prog", f, t)))

            def work():
                try:
                    ok, msg = self.proc.run()
                    if not ok or not os.path.isfile(wav):
                        self.q.put(("pdone", False, msg or "Sinov bajarilmadi", ""))
                        return
                    self.q.put(("prog", None, "Sinov video yig'ilmoqda..."))
                    make_preview(self.ffmpeg, st.src, st.stream, wav, st.test_start, st.test_len, out,
                                 log=lambda m: self.q.put(("log", m)))
                    self.q.put(("pdone", True, "", out))
                except Exception as e:                                  # noqa
                    self.q.put(("pdone", False, str(e)[:600], ""))
            self.worker = threading.Thread(target=work, daemon=True)
            self.worker.start()

        def _preview_done(self, ok, msg, path):
            self.btn_start.configure(state="normal")
            self.btn_prev.configure(state="normal")
            self.btn_stop.configure(state="disabled")
            self.pb.configure(mode="determinate")
            if ok:
                self.pb["value"] = 1000
                self.lbl_pct.configure(text="100%")
                self.lbl_stat.configure(text="Sinov tayyor \u2714")
                self.log("SINOV TAYYOR: " + path)
                self.log("Player'da 'Audio yo'li' ni almashtirib solishtiring: 1) NATIJA, 2) ORIGINAL. "
                         "Yoqmasa sozlamani o'zgartirib, 'Sinov ko'rish' ni qayta bosing; yaxshi bo'lsa START.")
                if not open_file(path):
                    messagebox.showinfo(APP_NAME, "Sinov video tayyor:\n" + path)
            else:
                self.lbl_stat.configure(text="To'xtatildi" if "To'xtat" in msg else "Xato")
                if "To'xtat" not in msg:
                    messagebox.showerror(APP_NAME, msg[:900])

        def _lic_tick(self):
            """Dastur ochiq turganda ham muddatni qayta tekshiradi."""
            ok, _i, msg = lic_status(True)
            if not ok:
                try:
                    messagebox.showerror(APP_NAME, msg + "\n\nDastur yopiladi.")
                finally:
                    self.destroy()
                return
            self.after(240000, self._lic_tick)

        def _open_tool(self, key, cls):
            try:
                lic_require()
            except RuntimeError as e:
                messagebox.showerror(APP_NAME, str(e))
                return
            w = self.tools.get(key)
            try:
                if w is not None and w.winfo_exists():
                    w.deiconify()
                    w.lift()
                    w.focus_force()
                    return
            except Exception:
                pass
            self.tools[key] = cls(self)

        def _open_intro(self):
            self._open_tool("intro", self.IntroWin)

        def _open_dl(self):
            self._open_tool("dl", self.DlWin)

        def _open_upd(self):
            self._open_tool("upd", self.UpdWin)

        def _auto_update_check(self):
            """Dastur ochilganda orqa fonda yangilanishni tekshiradi (manzil kiritilgan bo'lsa)."""
            cfg = upd_cfg_load()
            url = (cfg.get("url") or "").strip()
            if not url or not cfg.get("auto", True):
                return
            res = {}

            def w():
                try:
                    res["r"] = upd_check(url)
                except Exception:
                    res["r"] = None
            threading.Thread(target=w, daemon=True).start()

            def poll(n=0):
                if "r" not in res:
                    if n < 120:
                        self.after(500, poll, n + 1)
                    return
                r = res["r"]
                if r and r["newer"]:
                    self.nav_btns["Yangilash"].configure(text=" Yangilash  \u25cf")
                    self.log("Yangi versiya mavjud: %s (hozir %s). Tepadagi 'Yangilash' tugmasini bosing." % (r["version"], APP_VERSION))
            self.after(1500, poll)

        def _about(self):
            dlg = tk.Toplevel(self)
            dlg.title("Haqida")
            dlg.configure(bg=BG)
            dlg.transient(self)
            dlg.resizable(False, False)
            tk.Label(dlg, image=logo_image(96, dlg), bg=BG).pack(padx=40, pady=(22, 6))
            tk.Label(dlg, text=APP_NAME + "  v" + APP_VERSION, bg=BG, fg="white", font=("Segoe UI", 18, "bold")).pack()
            tk.Label(dlg, text="Dublyaj studiyalari uchun professional vositalar to'plami", bg=BG, fg=MUTED).pack(pady=(2, 4))
            tk.Label(dlg, text="Dasturchi: Muhammad Ali", bg=BG, fg="white", font=("Segoe UI", 11, "bold")).pack(pady=(0, 4))
            _ok, _li, _m = lic_status()
            if _ok:
                tk.Label(dlg, text="Litsenziya: %s  |  %d kun qoldi  |  ID: %s" % (_li["name"], _li["days_left"], machine_id_str()),
                         bg=BG, fg=GREEN, font=("Segoe UI", 9)).pack(pady=(0, 10))
            for t in ("•  Dublyaj: original vokalni o'chirish, ducking, 5.1 / 2.0, tez AI (MDX-Net)",
                      "•  Intro qo'shuvchi: kino boshiga reklama (kino sifati o'zgarmaydi)",
                      "•  Yuklovchi: M3U8 (HLS), to'g'ridan-to'g'ri havolalar, video sahifalar"):
                tk.Label(dlg, text=t, bg=BG, fg=FG, anchor="w").pack(fill="x", padx=30, pady=1)

            def save_icon():
                p = filedialog.asksaveasfilename(parent=dlg, defaultextension=".ico", initialfile="dublyaj_studio.ico",
                                                 filetypes=[("Icon", "*.ico")])
                if p:
                    save_ico(p)
                    messagebox.showinfo(APP_NAME, "Ikonka saqlandi:\n" + p, parent=dlg)
            bf = ttk.Frame(dlg)
            bf.pack(pady=16)
            ttk.Button(bf, text="Ikonkani saqlash (.ico)", command=save_icon).pack(side="left", padx=4)
            ttk.Button(bf, text="Yopish", style="Accent.TButton", command=dlg.destroy).pack(side="left", padx=4)

        def _open_batch(self):
            if getattr(self, "batch", None) is not None:
                try:
                    self.batch.deiconify()
                    self.batch.lift()
                    self.batch.focus_force()
                    return
                except Exception:
                    self.batch = None
            self.batch = BatchWindow(self)

        def _stop(self):
            if self.proc:
                self.log("To'xtatilmoqda...")
                self.btn_stop.configure(state="disabled")
                self.proc.abort()

        def _finish(self, ok, msg):
            self.btn_start.configure(state="normal")
            self.btn_prev.configure(state="normal")
            self.btn_stop.configure(state="disabled")
            self.pb.configure(mode="determinate")
            if ok:
                self.pb["value"] = 1000
                self.lbl_pct.configure(text="100%")
                self.lbl_stat.configure(text="Tayyor ✔")
                messagebox.showinfo(APP_NAME, f"Tayyor!\n\n{msg}")
            else:
                self.lbl_stat.configure(text="To'xtatildi" if "To'xtat" in msg else "Xato")
                if "To'xtat" not in msg:
                    messagebox.showerror(APP_NAME, msg[:900])

        def _close(self):
            if self.worker and self.worker.is_alive():
                if not messagebox.askyesno(APP_NAME, "Ishlov davom etmoqda. To'xtatib chiqilsinmi?"):
                    return
                self.proc.abort()
                self.worker.join(timeout=3)
            self._save_cfg()
            self.destroy()

    def license_gate():
        """Aktivlashtirish oynasi: to'g'ri kalit kiritilmaguncha dastur ochilmaydi, oyna yopilsa dastur yopiladi."""
        ok, _i, _m = lic_status(True)
        if ok:
            return True
        root = tk.Tk()
        root.title("Aktivlashtirish — " + APP_NAME)
        root.configure(bg=BG)
        root.resizable(False, False)
        w, h = 600, 560
        root.geometry("%dx%d+%d+%d" % (w, h, (root.winfo_screenwidth() - w) // 2, max(20, (root.winfo_screenheight() - h) // 2 - 30)))
        try:
            root.iconphoto(False, logo_image(64, root))
        except Exception:
            pass
        res = {"ok": False}
        tk.Label(root, image=logo_image(80, root), bg=BG).pack(pady=(22, 4))
        tk.Label(root, text="Dasturni aktivlashtirish", bg=BG, fg="white", font=("Segoe UI", 18, "bold")).pack()
        tk.Label(root, text="Dasturni ishlatish uchun litsenziya kalitini kiriting.", bg=BG, fg=MUTED,
                 font=("Segoe UI", 10)).pack(pady=(2, 12))
        tk.Label(root, text="Sizning Mashina ID (kalit olish uchun dasturchiga yuboring):", bg=BG, fg=FG,
                 font=("Segoe UI", 9)).pack(anchor="w", padx=28)
        row = tk.Frame(root, bg=BG)
        row.pack(fill="x", padx=28, pady=(2, 10))
        mid = tk.Entry(row, font=("Consolas", 13, "bold"), relief="flat", bg="#14151a", fg="#7fd1ff",
                       readonlybackground="#14151a", justify="center")
        mid.insert(0, machine_id_str())
        mid.configure(state="readonly")
        mid.pack(side="left", fill="x", expand=True, ipady=6)

        def copy_id():
            root.clipboard_clear()
            root.clipboard_append(machine_id_str())
            st.configure(text="Mashina ID nusxalandi.", fg=GREEN)
        tk.Button(row, text="Nusxalash", command=copy_id, relief="flat", bg="#2f3140", fg=FG, activebackground="#3a3d4c",
                  activeforeground="white", padx=12).pack(side="left", padx=(8, 0), ipady=3)
        tk.Label(root, text="Litsenziya kaliti:", bg=BG, fg=FG, font=("Segoe UI", 9)).pack(anchor="w", padx=28)
        txt = tk.Text(root, height=6, wrap="char", font=("Consolas", 10), relief="flat", bg="#14151a", fg=FG,
                      insertbackground="white", highlightthickness=1, highlightbackground="#3a3d4c", highlightcolor=ACC,
                      padx=8, pady=6)
        txt.pack(fill="x", padx=28, pady=(2, 6))
        st = tk.Label(root, text="", bg=BG, fg=RED, wraplength=540, justify="left", font=("Segoe UI", 10))
        st.pack(anchor="w", padx=28, pady=(0, 6))

        def go(_e=None):
            k = txt.get("1.0", "end").strip()
            if not k:
                st.configure(text="Kalitni kiriting.", fg=RED)
                return "break"
            try:
                lic_activate(k)
            except ValueError as e:
                st.configure(text=str(e), fg=RED)
                return "break"
            except Exception as e:                      # noqa
                st.configure(text="Xato: " + str(e)[:200], fg=RED)
                return "break"
            res["ok"] = True
            root.destroy()
            return "break"
        bf = tk.Frame(root, bg=BG)
        bf.pack(pady=(6, 10))
        tk.Button(bf, text="Aktivlashtirish", command=go, relief="flat", bg=ACC, fg="white", activebackground="#6aa0ff",
                  activeforeground="white", font=("Segoe UI", 11, "bold"), padx=26, pady=8).pack(side="left", padx=6)
        tk.Button(bf, text="Chiqish", command=root.destroy, relief="flat", bg="#3a3d4c", fg=FG, activebackground="#4a4e60",
                  activeforeground="white", font=("Segoe UI", 11), padx=26, pady=8).pack(side="left", padx=6)
        tk.Label(root, text="Dasturchi: Muhammad Ali", bg=BG, fg=MUTED, font=("Segoe UI", 9)).pack(side="bottom", pady=8)
        txt.focus_set()
        root.protocol("WM_DELETE_WINDOW", root.destroy)
        root.mainloop()
        try:
            root.destroy()
        except Exception:
            pass
        return res["ok"] and lic_status(True)[0]

    if not license_gate():
        return
    app = App()
    if on_ready:
        app.after(300, lambda: on_ready(app))
    app.mainloop()


def make_preview(ffmpeg, src, stream, wav, start, length, out, log=None):
    """Sinov video: original videoning shu qismi + 2 ta audio yo'l (1: NATIJA, 2: ORIGINAL). Player'da yo'lni almashtirib solishtiring."""
    cmd = [ffmpeg, "-y", "-v", "error", "-nostdin", "-ss", "%.3f" % start, "-t", "%.3f" % length, "-i", src,
           "-i", wav, "-map", "0:v:0?", "-map", "1:a:0", "-map", "0:a:%d" % stream,
           "-c:v", "libx264", "-preset", "ultrafast", "-crf", "27", "-pix_fmt", "yuv420p",
           "-vf", "scale=-2:'min(720,ih)'", "-sn", "-dn",
           "-c:a", "ac3", "-b:a", "448k",
           "-metadata:s:a:0", "title=NATIJA (dublyaj bilan)", "-metadata:s:a:1", "title=ORIGINAL (asl ovoz)",
           "-disposition:a:0", "default", "-disposition:a:1", "0", out]
    if log:
        log("Sinov video yig'ilmoqda (video + natija + original)...")
    r = subprocess.run(cmd, capture_output=True, text=True, errors="replace", **({"creationflags": 0x08000000} if os.name == "nt" else {}))
    if r.returncode != 0 or not os.path.isfile(out):
        raise RuntimeError("Sinov video yaratilmadi: " + (r.stderr or "")[-400:])
    return out


def open_file(path):
    try:
        if os.name == "nt":
            os.startfile(path)                                    # noqa
        elif sys.platform == "darwin":
            subprocess.Popen(["open", path])
        else:
            subprocess.Popen(["xdg-open", path])
        return True
    except Exception:
        return False


def run_bench():
    lines = [f"{APP_NAME} {APP_VERSION} - AI tezlik sinovi", f"CPU oqimlar soni: {os.cpu_count()}"]
    try:
        import onnxruntime as ort
        lines.append(f"onnxruntime {ort.__version__}, mavjud qurilmalar: {ort.get_available_providers()}")
        m = MDX("fast")
        dev = m.prov.replace("ExecutionProvider", "")
        x = (np.random.RandomState(1).randn(m.chunk, 2) * 0.05).astype(np.float32)
        m.vocals_many([x] * m.n)                                    # isitish
        t0 = time.time()
        reps = 3
        for _ in range(reps):
            m.vocals_many([x] * m.n)
        per = (time.time() - t0) / (reps * m.n)                     # bitta bo'lak uchun samarali vaqt
        blk = m.chunk / MDX_SR
        per_hour = per * (3600 / blk) * 0.85
        lines += [f"AI qurilma: {dev}, parallel oqimlar: {m.n}",
                  f"Bitta bo'lak ({blk:.1f} s audio): {per:.2f} s",
                  f"1 soatlik kino uchun AI vaqti taxminan: {per_hour / 60:.1f} daqiqa (5.1 markaz kanal, dublyaj ~85% bo'lsa)"]
    except Exception as e:                                         # noqa
        lines.append("XATO: " + str(e)[:300])
    txt = "\n".join(lines)
    try:
        d = os.path.join(os.path.expanduser("~"), ".dublyaj_studio")
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, "bench.txt"), "w", encoding="utf-8") as f:
            f.write(txt)
    except OSError:
        pass
    print(txt)
    try:
        import tkinter as tk
        from tkinter import messagebox
        r = tk.Tk()
        r.withdraw()
        messagebox.showinfo("AI tezlik sinovi", txt)
        r.destroy()
    except Exception:
        pass


def main():
    import multiprocessing
    multiprocessing.freeze_support()
    if "--version" in sys.argv:
        print(APP_NAME, APP_VERSION)
        return
    if "--bench" in sys.argv:                     # AI tezlik sinovi: natija bench.txt ga yoziladi va oynada ko'rsatiladi
        run_bench()
        return
    if "--selftest" in sys.argv:                  # EXE to'g'ri yig'ilganini tekshirish: natija selftest.txt ga yoziladi
        lines = [f"{APP_NAME} {APP_VERSION}  (frozen={FROZEN})", f"app_dir: {app_dir()}"]
        for t in ("ffmpeg", "ffprobe", "yt-dlp"):
            lines.append(f"{t}: {find_tool(t) or 'TOPILMADI'}")
        for k in MDX_MODELS:
            lines.append(f"model {k}: {mdx_find(k) or 'yo`q (birinchi ishlatishda yuklanadi)'}")
        try:
            import onnxruntime as ort
            lines.append(f"onnxruntime {ort.__version__}: {ort.get_available_providers()}")
            if mdx_find("fast"):
                m = MDX("fast")
                t0 = time.time()
                m.vocals(np.zeros((m.chunk, 2), np.float32))
                lines.append(f"AI sinovi OK: {m.prov}, {m.n} sessiya, 1 bo'lak {time.time() - t0:.2f} s")
        except Exception as e:                    # noqa
            lines.append(f"onnxruntime XATO: {e}")
        try:
            import scipy
            lines.append(f"scipy {scipy.__version__}")
        except Exception as e:                    # noqa
            lines.append(f"scipy yo'q: {e}")
        try:
            import tkinter
            lines.append(f"tkinter {tkinter.TkVersion}")
        except Exception as e:                    # noqa
            lines.append(f"tkinter XATO: {e}")
        txt = "\n".join(lines)
        try:
            with open(os.path.join(app_dir(), "selftest.txt"), "w", encoding="utf-8") as f:
                f.write(txt + "\n")
        except OSError:
            pass
        print(txt)
        return
    if "--make-icon" in sys.argv:                 # build uchun: .ico yaratish
        i = sys.argv.index("--make-icon")
        save_ico(sys.argv[i + 1] if len(sys.argv) > i + 1 else "dublyaj_studio.ico")
        return
    if sys.stdout is None:                        # --windowed .exe da konsol yo'q
        sys.stdout = open(os.devnull, "w")
    if sys.stderr is None:
        sys.stderr = open(os.devnull, "w")
    if os.name == "nt":                           # aniq (blur bo'lmagan) interfeys: High-DPI
        try:
            import ctypes
            try:
                ctypes.windll.shcore.SetProcessDpiAwareness(1)
            except Exception:
                ctypes.windll.user32.SetProcessDPIAware()
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("DublyajStudio.App")   # vazifalar panelida o'z ikonkasi
        except Exception:
            pass
    run_gui()


if __name__ == "__main__":
    main()

# DS-SIG:0f1ad81ee2a68fb3a1d7a5e848d057717aacb2d4beb494de9eb7fff5aaeef4ac0e653df8fe5597bc82647b5b83a7a717d3b3a33b19c2506adec6ec71da877d03
