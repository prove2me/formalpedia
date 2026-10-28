-- Prove2me | Theorems.Thm_BitcoinScript_serialize_roundtrip
-- name    : BitcoinScript.serialize_roundtrip
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T05:42:53.452028+00:00
-- url     : https://prove2.me/theorems/73ea1919-d6db-4777-ad70-7be53dfe142f
-- title:
--   CScriptNum serialization round-trips
-- statement:
--   For every integer $n$, $\mathrm{setVch}(\mathrm{serialize}(n)) = n$: reading back the bytes `CScriptNum::serialize` produces gives the original value, including $0$ (the empty encoding), negative values (sign bit or sign byte), and magnitudes whose top byte already has bit 7 set (sign byte appended).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CastToBool (lines 46-59), EvalScript (417-1249), EvalChecksigPreTapscript, VerifyScript (2012-2110), src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScriptNum (227-382), opcodetype, MAX_SCRIPT_ELEMENT_SIZE, MAX_OPS_PER_SCRIPT, MAX_PUBKEYS_PER_MULTISIG, MAX_STACK_SIZE, src/script/script.h; GetScriptOp, IsPushOnly, IsPayToScriptHash, src/script/script.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.h

import Definitions.Def_BitcoinScript

theorem BitcoinScript.serialize_roundtrip (n : Int) : BitcoinScript.setVch (BitcoinScript.serialize n) = n := by sorry
