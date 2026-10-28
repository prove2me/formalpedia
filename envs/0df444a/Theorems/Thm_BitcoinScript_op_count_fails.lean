-- Prove2me | Theorems.Thm_BitcoinScript_op_count_fails
-- name    : BitcoinScript.op_count_fails
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T05:44:19.975834+00:00
-- url     : https://prove2.me/theorems/7400f3ee-0460-483b-9bfa-d3268036c34c
-- title:
--   More than 201 operations never succeed
-- statement:
--   For every flag setting, oracle, starting stack and script with more than $201$ counted opcodes — non-push opcodes above `OP_16`, which is exactly what `nOpCount` counts (`OP_1NEGATE`, `OP_RESERVED` and `OP_1`…`OP_16` are exempt) — $\mathrm{evalScript}$ returns `none`. Each counted opcode, executed or skipped, raises `nOpCount` by one and the limit is checked before every one of them.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CastToBool (lines 46-59), EvalScript (417-1249), EvalChecksigPreTapscript, VerifyScript (2012-2110), src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScriptNum (227-382), opcodetype, MAX_SCRIPT_ELEMENT_SIZE, MAX_OPS_PER_SCRIPT, MAX_PUBKEYS_PER_MULTISIG, MAX_STACK_SIZE, src/script/script.h; GetScriptOp, IsPushOnly, IsPayToScriptHash, src/script/script.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.h

import Definitions.Def_BitcoinScript

theorem BitcoinScript.op_count_fails (f : Flags) (o : Oracle) (stack : List Bytes) (script : Script)
    (h : BitcoinScript.MAX_OPS_PER_SCRIPT < BitcoinScript.opsIn script) :
    BitcoinScript.evalScript f o stack script = none := by sorry
