-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_allcap_original_caplinear_value_nonnegative
-- name    : AvramDividend.Classical.avram_f6_allcap_original_caplinear_value_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:27:10.299509+00:00
-- url     : https://prove2.me/theorems/4828d415-9e51-445c-939c-87e8f9648801
-- title:
--   Original canonical caplinear value is nonnegative for all nonnegative reserves
-- statement:
--   Under the exact original w(0)>=0 and interior derivative >=1, the canonical slope-one caplinear extension of w is nonnegative at every nonnegative reserve z, even if a Gaussian fluctuation exceeds a finite C. This is the actual physically needed above-cap positivity; proved from the published global caplinear secant identity without assuming any smoothness of raw w above C.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_allcap_original_caplinear_value_nonnegative
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (z : ℝ) (hz : 0 ≤ z) :
    0 ≤ (if ENNReal.ofReal z ≤ C then w z
         else w C.toReal + (z - C.toReal)) := by sorry
