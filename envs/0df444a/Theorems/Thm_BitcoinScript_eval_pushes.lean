-- Prove2me | Theorems.Thm_BitcoinScript_eval_pushes
-- name    : BitcoinScript.eval_pushes
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T05:43:51.312859+00:00
-- url     : https://prove2.me/theorems/acfe7846-bfcd-42bc-bd41-1dd42b943e2a
-- title:
--   A push-only script leaves exactly its pushes
-- statement:
--   For every flag setting and oracle and every list of elements $p_1, \dots, p_n$ each of at most $520$ bytes with $n \le 1000$, evaluating the script $\langle p_1\rangle \cdots \langle p_n\rangle$ from the empty stack succeeds with stack $[p_n, \dots, p_1]$ (top first). This is the evaluation of a standard `scriptSig`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CastToBool (lines 46-59), EvalScript (417-1249), EvalChecksigPreTapscript, VerifyScript (2012-2110), src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScriptNum (227-382), opcodetype, MAX_SCRIPT_ELEMENT_SIZE, MAX_OPS_PER_SCRIPT, MAX_PUBKEYS_PER_MULTISIG, MAX_STACK_SIZE, src/script/script.h; GetScriptOp, IsPushOnly, IsPayToScriptHash, src/script/script.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.h

import Definitions.Def_BitcoinScript

theorem BitcoinScript.eval_pushes (f : Flags) (o : Oracle) (ps : List Bytes)
    (hsz : ∀ p ∈ ps, p.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hlen : ps.length ≤ BitcoinScript.MAX_STACK_SIZE) :
    BitcoinScript.evalScript f o [] (ps.map Instr.push) = some ps.reverse := by sorry
