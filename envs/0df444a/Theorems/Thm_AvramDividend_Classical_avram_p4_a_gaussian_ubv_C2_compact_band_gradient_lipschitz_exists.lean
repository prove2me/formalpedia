-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_C2_compact_band_gradient_lipschitz_exists
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ubv_C2_compact_band_gradient_lipschitz_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:42:35.907825+00:00
-- url     : https://prove2.me/theorems/d82e31f6-4bb3-4ca4-bc38-2eabf9188e1b
-- title:
--   Original UBV strict C2 interior automatically gives finite compact-band gradient Lipschitz constant
-- statement:
--   For any C2 test w on the exact positive below-cap interior of the original dividend problem and any compact interval contained in that open interior, there exists a finite nonnegative Lipschitz constant for w' on that interval. The proof obtains a uniform second-derivative bound from continuity and compactness, then applies convex-interval derivative control. This is the automatic deterministic envelope used in Gaussian integrand mesh localisation; no global C2, Brownian representation, endpoint occupation or jump assumptions.
-- source:
--   Avram–Palmowski–Pistorius Proposition 4(i), C2 only on (0,C); pinned Mathlib ContDiffAt.derivWithin and IsCompact.exists_bound_of_continuousOn and Convex.lipschitzOnWith_of_nnnorm_deriv_le.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ubv_C2_compact_band_gradient_lipschitz_exists
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ K : ℝ≥0, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |deriv w s - deriv w t| ≤ (K : ℝ) * |s - t| := by sorry
