-- Prove2me | solution 2 for moebius_summatory_rpow_bound_below_record
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:30:38.98459+00:00
-- url     : https://prove2.me/submissions/a21f874f-276c-45b2-aed7-5057c4d03dbf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis



theorem solution :
    ∀ ε : ℝ, 0 < ε → ε ≤ 0.3749570698 →
      Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε)) :=
  fun ε hε _ => moebius_summatory_rpow_bound_of_riemannHypothesis mathlib_riemannHypothesis ε hε
