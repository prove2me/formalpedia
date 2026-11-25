-- Prove2me | Theorems.Thm_DetDLP_m89_s1_word_pipe
-- name    : DetDLP.m89_s1_word_pipe
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T00:32:38.305544+00:00
-- url     : https://prove2.me/theorems/64aed7a7-32da-4fa7-b0df-eca5b6b6ad2b
-- title:
--   Compose two Stage I word machines with a fixed space policy
-- statement:
--   For a positive field bit length, run two word transducers in sequence. Uniform Stage I time is preserved. If both space bounds are polynomial then the composite has polynomial space; otherwise this statement uses the Stage I bound for both stages. The machines may have arbitrary garbage on work tapes.
-- source:
--   S. Liu, B. Zhang, and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2 (pp. 11–13), proof of Theorem 3.1; Stage I machine model of Section 2.

import Definitions.Def_DetDLP_Machine
set_option autoImplicit false
open DetDLP
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m89_s1_word_pipe (A : PrimitiveMachine) (a : Fin A.tapeCount) (B : PrimitiveMachine) (d : Fin B.tapeCount)
    (i j : ℕ) (small : Bool) : ∃ (M : PrimitiveMachine) (o : Fin M.tapeCount) (K : ℕ),
      ∀ (b : ℕ), 1 ≤ b → ∀ x y z : List Bool,
        RunsWithin A a x y (mainSpaceBound i b) (if small then polyBound i b else mainSpaceBound i b) →
        RunsWithin B d y z (mainSpaceBound j b) (if small then polyBound j b else mainSpaceBound j b) →
        RunsWithin M o x z (mainSpaceBound K b) (if small then polyBound K b else mainSpaceBound K b) := by sorry
