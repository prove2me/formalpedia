-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite53_original_interior_C2_derivative_certificates
-- name    : AvramDividend.Classical.avram_gfinite53_original_interior_C2_derivative_certificates
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T22:26:04.610993+00:00
-- url     : https://prove2.me/theorems/3a24d191-410e-4582-bc6b-ea13a7989ec1
-- title:
--   Original finite-cap interior C2 supplies both real derivative certificates
-- statement:
--   Under the exact original smoothness hypothesis on 0<y and ENNReal.ofReal y<C, establish the usual HasDerivAt certificate for w and the second-derivative HasDerivAt certificate for deriv w. These are the missing exact-format assumptions required to apply the proved Gaussian HJB uniform-gradient bound at interior reserve levels.

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gfinite53_original_interior_C2_derivative_certificates
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (y : ℝ) (hy0 : 0 < y) (hyC : ENNReal.ofReal y < C) :
    HasDerivAt w (deriv w y) y ∧
      HasDerivAt (deriv w) (iteratedDeriv 2 w y) y := by
  sorry
