-- Prove2me | solution 2 for moebius_dirichlet_series_holomorphic_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:26:14.303337+00:00
-- url     : https://prove2.me/submissions/2261758a-b56e-4902-8ee4-019fabd09503
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_riemann_hypothesis_iff_moebius_holomorphic_extension

theorem solution :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        F s = LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s :=
  riemann_hypothesis_iff_moebius_holomorphic_extension.mp mathlib_riemannHypothesis
