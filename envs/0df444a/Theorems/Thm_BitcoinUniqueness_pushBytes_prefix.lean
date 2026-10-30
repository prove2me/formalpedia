-- Prove2me | Theorems.Thm_BitcoinUniqueness_pushBytes_prefix
-- name    : BitcoinUniqueness.pushBytes_prefix
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T13:47:01.222083+00:00
-- url     : https://prove2.me/theorems/25b67b58-2553-4a00-b00b-cccdafaa722e
-- title:
--   A push is never a proper prefix of another push
-- statement:
--   For byte strings $d, d'$ shorter than $2^{32}$: if the canonical push of $d$ is a prefix of the canonical push of $d'$ then $d = d'$. The first byte fixes the encoding class (direct, `PUSHDATA1/2/4`) and, with the length field, the length.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: ConnectBlock (fEnforceBIP30, BIP34_IMPLIES_BIP30_LIMIT), ContextualCheckBlock (the BIP34 height push), src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CScript::push_int64, CScriptNum::serialize (script/script.h); BIP30, BIP34

import Definitions.Def_BitcoinUniqueness
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinUniqueness BitcoinSer BitcoinBlockV2

theorem BitcoinUniqueness.pushBytes_prefix (d d' : BitcoinSer.Bytes) (hd : d.length < 2 ^ 32) (hd' : d'.length < 2 ^ 32)
    (h : (BitcoinSig.pushBytes d).isPrefixOf (BitcoinSig.pushBytes d') = true) : d = d' := by sorry
