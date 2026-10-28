-- Prove2me | Theorems.Thm_BitcoinScript_disabled_fails
-- name    : BitcoinScript.disabled_fails
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T05:44:01.147092+00:00
-- url     : https://prove2.me/theorems/7f687f0f-4c6a-4cce-a438-2cae467b6320
-- title:
--   A disabled opcode fails the script wherever it appears
-- statement:
--   For every flag setting, oracle, script, and state, if the script contains any of the fifteen disabled opcodes (`CAT`, `SUBSTR`, `LEFT`, `RIGHT`, `INVERT`, `AND`, `OR`, `XOR`, `2MUL`, `2DIV`, `MUL`, `DIV`, `MOD`, `LSHIFT`, `RSHIFT`), running it fails — even when the opcode sits in a branch that would not execute. This is the CVE-2010-5137 rule.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CastToBool (lines 46-59), EvalScript (417-1249), EvalChecksigPreTapscript, VerifyScript (2012-2110), src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScriptNum (227-382), opcodetype, MAX_SCRIPT_ELEMENT_SIZE, MAX_OPS_PER_SCRIPT, MAX_PUBKEYS_PER_MULTISIG, MAX_STACK_SIZE, src/script/script.h; GetScriptOp, IsPushOnly, IsPayToScriptHash, src/script/script.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.h

import Definitions.Def_BitcoinScript

theorem BitcoinScript.disabled_fails (f : Flags) (o : Oracle) (script : Script) (c : Byte)
    (hc : BitcoinScript.isDisabled c = true) (hmem : Instr.op c ∈ script) :
    ∀ s : State, BitcoinScript.run f o s script = none := by sorry
