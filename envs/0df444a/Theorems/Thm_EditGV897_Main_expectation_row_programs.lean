-- Prove2me | Theorems.Thm_EditGV897_Main_expectation_row_programs
-- name    : EditGV897.Main.expectation_row_programs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T03:36:28.19503+00:00
-- url     : https://prove2.me/theorems/674a4770-332c-40a9-8802-020cdc7ea334
-- title:
--   Finite tape programs for conditional expectations and greedy rows
-- statement:
--   There are fixed finite binary tape programs for exact doubled conditional-expectation evaluation and the prescribed greedy row construction in Lemma 1. Let $F$ be a family of $M$ affine edit maps on $n$ bits and let $G$ have at most $n$ parity rows. For every legal row prefix, the evaluator computes its doubled conditional expectation in the specified signed integer representation. The row builder computes the deterministic row obtained by repeatedly selecting the minimizing next bit.
--
--   Uniform natural constants $A>0,d$ bound both actual halting executions by
--
--   $$A(n+M+1)^d.$$
--
--   The count charges all parsing, Gaussian elimination, binary arithmetic and output writing. This isolates the two applications of the exact affine counter from the counting subroutine itself.
-- source:
--   Gabrys, Singhvi, Yaakobi, Making Every Edit Count, STOC 2027 submission #897, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, §3.2 Gaussian elimination and §4.1 Lemma 1, printed pp.8–10 / PDF pp.9–11

import Definitions.Def_EditGV897_Main_Construction
open EditGV897.Main

theorem EditGV897.Main.expectation_row_programs :
    ∃ (evaluator rowBuilder : Program) (A d : ℕ), 0 < A ∧
      ∀ (n t : ℕ) (F : Family n) (G : Rows n),
        1 ≤ t → EditFamily t F → G.length ≤ n →
        (∀ p : List Bit, p.length ≤ n →
          Runs evaluator (expectationInput F G p) (integerCode (twiceExpectation F G p))
            (polyBudget A d (n + F.length))) ∧
        Runs rowBuilder (familyRowsInput F G) (wordCode (chooseRow F G))
          (polyBudget A d (n + F.length)) := by sorry
