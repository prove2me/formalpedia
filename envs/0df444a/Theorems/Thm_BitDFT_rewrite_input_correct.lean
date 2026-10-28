-- Prove2me | Theorems.Thm_BitDFT_rewrite_input_correct
-- name    : BitDFT.rewrite_input_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:40:38.175968+00:00
-- url     : https://prove2.me/theorems/798097b8-0df4-4d2d-9120-e7a8f4344e26
-- title:
--   Rewrite the complete native input within 19q+|r|+2 transitions
-- statement:
--   For n,b≥1 and binary suffix r, set q=b+3 max(ceil(log₂ n),1)+5. From ordinary native input encNat(n)encNat(b)r, a single fixed machine halts with exact output encNat(n)encNat(q)r within 19q+|r|+2 transitions. The full final configuration is specified: input is preserved with its head at the separator, output is exact including its blank tail, and retained work tapes and heads are identified. The precision word used internally has value q and length at most q.
-- source:
--   Complete actual-machine input conversion for the integer-multiplication-to-DFT wrapper. The arbitrary Fourier-machine invocation and multiplier-based output scaling remain separate construction obligations.

import Definitions.Def_BitDFT_RewriteInput
open BitDFT BitDFT.RewriteInput IntMul

theorem BitDFT.rewrite_input_correct (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (rest : List Bool) :
    let q := guardPrecision n b
    let x := encNat n ++ encNat b ++ rest
    ∃ t v, t ≤ 19*q+rest.length+2 ∧ BinaryCounter.value v = q ∧ v.length ≤ q ∧
      machine.step^[t] (machine.initCfg x []) = final n b rest v := by sorry
