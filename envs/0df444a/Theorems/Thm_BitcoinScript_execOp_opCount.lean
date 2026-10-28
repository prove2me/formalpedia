-- Prove2me | Theorems.Thm_BitcoinScript_execOp_opCount
-- name    : BitcoinScript.execOp_opCount
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T05:44:10.942357+00:00
-- url     : https://prove2.me/theorems/99756895-49e3-4273-8645-10ddfa12c2eb
-- title:
--   No opcode lowers the operation count
-- statement:
--   For every flag setting, oracle, execution flag, opcode $c$ and states $s, s'$ with $\mathrm{execOp}(c, s) = \mathrm{some}\ s'$: $s.\mathrm{opCount} \le s'.\mathrm{opCount}$, and either the count is unchanged or (for `CHECKMULTISIG`, which adds its key count) it is at most $201$. A case analysis over the whole opcode table.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CastToBool (lines 46-59), EvalScript (417-1249), EvalChecksigPreTapscript, VerifyScript (2012-2110), src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScriptNum (227-382), opcodetype, MAX_SCRIPT_ELEMENT_SIZE, MAX_OPS_PER_SCRIPT, MAX_PUBKEYS_PER_MULTISIG, MAX_STACK_SIZE, src/script/script.h; GetScriptOp, IsPushOnly, IsPayToScriptHash, src/script/script.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.h

import Definitions.Def_BitcoinScript

theorem BitcoinScript.execOp_opCount (f : Flags) (o : Oracle) (e : Bool) (c : Byte) (s s' : State)
    (h : BitcoinScript.execOp f o e c s = some s') :
    s.opCount ≤ s'.opCount ∧ (s'.opCount = s.opCount ∨ s'.opCount ≤ BitcoinScript.MAX_OPS_PER_SCRIPT) := by sorry
