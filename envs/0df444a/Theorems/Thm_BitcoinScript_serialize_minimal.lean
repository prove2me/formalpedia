-- Prove2me | Theorems.Thm_BitcoinScript_serialize_minimal
-- name    : BitcoinScript.serialize_minimal
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T05:43:09.983221+00:00
-- url     : https://prove2.me/theorems/8a5e9014-6265-447d-9aff-67cc70031662
-- title:
--   The serializer always produces a minimal encoding
-- statement:
--   For every integer $n$, $\mathrm{nonMinimal}(\mathrm{serialize}(n)) = \mathtt{false}$: the output of `CScriptNum::serialize` never has a final byte without value bits that the previous byte could absorb. Consequently the interpreter's own numeric results always pass the `MINIMALDATA` test.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CastToBool (lines 46-59), EvalScript (417-1249), EvalChecksigPreTapscript, VerifyScript (2012-2110), src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScriptNum (227-382), opcodetype, MAX_SCRIPT_ELEMENT_SIZE, MAX_OPS_PER_SCRIPT, MAX_PUBKEYS_PER_MULTISIG, MAX_STACK_SIZE, src/script/script.h; GetScriptOp, IsPushOnly, IsPayToScriptHash, src/script/script.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.h

import Definitions.Def_BitcoinScript

theorem BitcoinScript.serialize_minimal (n : Int) : BitcoinScript.nonMinimal (BitcoinScript.serialize n) = false := by sorry
