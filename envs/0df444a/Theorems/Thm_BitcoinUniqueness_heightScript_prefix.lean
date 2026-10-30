-- Prove2me | Theorems.Thm_BitcoinUniqueness_heightScript_prefix
-- name    : BitcoinUniqueness.heightScript_prefix
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T13:47:13.588628+00:00
-- url     : https://prove2.me/theorems/bec1ef70-5be3-4bbc-957d-e752384b1706
-- title:
--   BIP34 height pushes are prefix-free
-- statement:
--   For heights $a, b < 2^{31}$: if `CScript() << a` is a prefix of `CScript() << b` then $a = b$. The single-byte forms (`OP_0`, `OP_1`..`OP_16`) never prefix a data push and vice versa, and data pushes are prefix-free with `CScriptNum::serialize` injective.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: ConnectBlock (fEnforceBIP30, BIP34_IMPLIES_BIP30_LIMIT), ContextualCheckBlock (the BIP34 height push), src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CScript::push_int64, CScriptNum::serialize (script/script.h); BIP30, BIP34

import Definitions.Def_BitcoinUniqueness
open BitcoinUniqueness BitcoinSer BitcoinBlockV2

theorem BitcoinUniqueness.heightScript_prefix (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (h : (BitcoinBlockV2.heightScript a).isPrefixOf (BitcoinBlockV2.heightScript b) = true) : a = b := by sorry
