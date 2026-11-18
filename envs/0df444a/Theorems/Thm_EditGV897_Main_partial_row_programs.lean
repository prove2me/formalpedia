-- Prove2me | Theorems.Thm_EditGV897_Main_partial_row_programs
-- name    : EditGV897.Main.partial_row_programs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T02:47:31.883212+00:00
-- url     : https://prove2.me/theorems/9944b692-916d-427b-bbf3-082777f2b78f
-- title:
--   Finite tape programs for exact counts and conditional-expectation rows
-- statement:
--   There are fixed finite binary tape programs for the three computational tasks in Lemma 1: Gaussian affine-system counting, exact doubled conditional-expectation evaluation for every legal row prefix, and the prescribed minimizing-prefix row construction. Uniform natural constants $A>0,d$ bound their actual halting executions by
--
--   $$A(n+|E|+1)^d$$
--
--   for an equation list $E$, and by
--
--   $$A(n+M+1)^d$$
--
--   for an affine edit family of size $M$ and current parity rows of length at most $n$. Inputs and outputs use the specified unary dimensions and framed binary encodings. The transition count includes all parsing, elimination, binary integer arithmetic, and input/output work. This statement records the computational portion of Lemma 1 separately from its exact-counting identities and witness-halving guarantee.
-- source:
--   Gabrys, Singhvi, Yaakobi, Making Every Edit Count, STOC 2027 submission #897, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, §3.2 and §4.1, Lemma 1 and its proof, printed pp.8–10 / PDF pp.9–11

import Definitions.Def_EditGV897_Main_Construction
open EditGV897.Main

theorem EditGV897.Main.partial_row_programs :
    ∃ (counter evaluator rowBuilder : Program) (A d : ℕ), 0 < A ∧
      (∀ (n : ℕ) (E : List (Equation n)),
        Runs counter (unary n ++ equationCode E) (binary (affineCount E))
          (polyBudget A d (n + E.length))) ∧
      (∀ (n t : ℕ) (F : Family n) (G : Rows n),
        1 ≤ t → EditFamily t F → G.length ≤ n →
        (∀ p : List Bit, p.length ≤ n →
          Runs evaluator (expectationInput F G p) (integerCode (twiceExpectation F G p))
            (polyBudget A d (n + F.length))) ∧
        Runs rowBuilder (familyRowsInput F G) (wordCode (chooseRow F G))
          (polyBudget A d (n + F.length))) := by sorry
