-- Prove2me | Theorems.Thm_BitcoinScript_castToBool_iff
-- name    : BitcoinScript.castToBool_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T05:43:38.189989+00:00
-- url     : https://prove2.me/theorems/222c4e61-7c80-4a82-b311-e521acb2c8ae
-- title:
--   CastToBool is 'nonzero as a script number'
-- statement:
--   For every byte list $v$, $\mathrm{castToBool}(v) = \mathtt{true} \iff \mathrm{setVch}(v) \ne 0$. In particular both encodings of zero — all-zero bytes, and zero bytes followed by `0x80` (negative zero) — are false, and every other byte list is true, whatever its length.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CastToBool (lines 46-59), EvalScript (417-1249), EvalChecksigPreTapscript, VerifyScript (2012-2110), src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScriptNum (227-382), opcodetype, MAX_SCRIPT_ELEMENT_SIZE, MAX_OPS_PER_SCRIPT, MAX_PUBKEYS_PER_MULTISIG, MAX_STACK_SIZE, src/script/script.h; GetScriptOp, IsPushOnly, IsPayToScriptHash, src/script/script.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.h

import Definitions.Def_BitcoinScript

theorem BitcoinScript.castToBool_iff (v : Bytes) : BitcoinScript.castToBool v = true ↔ BitcoinScript.setVch v ≠ 0 := by sorry
