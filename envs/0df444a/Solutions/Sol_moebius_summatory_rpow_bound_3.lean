-- Prove2me | solution 3 for moebius_summatory_rpow_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:26:12.286031+00:00
-- url     : https://prove2.me/submissions/61a2de20-3fb6-4694-b157-ac5ccb9bc5f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis

theorem solution :
    ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε)) :=
  moebius_summatory_rpow_bound_of_riemannHypothesis mathlib_riemannHypothesis
