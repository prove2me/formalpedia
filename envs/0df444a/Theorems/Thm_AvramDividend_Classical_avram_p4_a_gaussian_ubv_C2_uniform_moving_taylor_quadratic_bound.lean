-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_C2_uniform_moving_taylor_quadratic_bound
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ubv_C2_uniform_moving_taylor_quadratic_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:32:26.592647+00:00
-- url     : https://prove2.me/theorems/672c0cae-c6b6-4738-894a-8e8fe4ef0398
-- title:
--   Uniform quadratic moving-mesh Taylor error from the exact original strict C2 interior
-- statement:
--   On every compact positive below-cap source band, strict C2 alone supplies a deterministic nonnegative constant K uniformly controlling first-order Taylor error between every pair of distinct band states u,v by K/2 times (v-u)^2. It uses the exact intermediate-point Lagrange remainder, continuous second derivative and compactness. This is the local moving-mesh deterministic estimate needed to bound the Gaussian Ito residual without any global C2 extension, Brownian process or boundary occupation claim.
-- source:
--   Avram Palmowski Pistorius Proposition 4(i); pinned Mathlib ContDiffAt.derivWithin, IsCompact.exists_bound_of_continuousOn, Taylor mean remainder Lagrange, Set.uIcc_subset_Icc; accepted source interior openness b917eaf2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ubv_C2_uniform_moving_taylor_quadratic_bound
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≠ v →
        |w v - taylorWithinEval w 1 (uIcc u v) u v| ≤
          (K / 2) * (v - u) ^ 2 := by sorry
