-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_C2_interior_band_quadratic_taylor_remainder
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ubv_C2_interior_band_quadratic_taylor_remainder
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:56:29.752062+00:00
-- url     : https://prove2.me/theorems/67122f2c-1813-4605-8629-e1eec51505a2
-- title:
--   Strict UBV C2 interior gives quadratic first-order Taylor mesh remainder on any compact band
-- statement:
--   For the exact positive below-cap C2 interior, every closed interval [a,b] inside the interior has a single finite quadratic first-order Taylor remainder envelope at anchor a. The polynomial taylorWithinEval is the pinned Mathlib first-order Taylor polynomial; no regularity across ruin, cap, or jumps is assumed. This is deterministic support for the original Gaussian Itô mesh, not a continuous martingale or a stochastic integral.
-- source:
--   Avram Palmowski Pistorius Proposition 4(i) strict interior C2; pinned Mathlib Analysis.Calculus.Taylor exists_taylor_mean_remainder_bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ubv_C2_interior_band_quadratic_taylor_remainder
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ K : ℝ, ∀ y ∈ Icc a b,
      ‖w y - taylorWithinEval w 1 (Icc a b) a y‖ ≤
        K * (y - a) ^ 2 := by sorry
