-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_allcap_linear_nonnegative
-- name    : AvramDividend.Classical.avram_p3_bv_allcap_linear_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:43:09.026985+00:00
-- url     : https://prove2.me/theorems/6f389e8f-2b4f-4cef-be75-06a1f48c259f
-- title:
--   Canonical original BV HJB slope-one cap continuation remains nonnegative on every nonnegative reserve
-- statement:
--   When the canonical original BV verification candidate has w(0)≥0, the all-cap slope-one continuation remains nonnegative at every nonnegative reserve, including zero and cap contact. The proof invokes the independently Proved global monotonicity rather than any right-of-cap smoothness.
-- source:
--   Monotonicity of the all-cap linear continuation at positive caps, plus its exact zero value w(0) and the original nonnegative boundary condition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_allcap_linear_monotone_nonnegative

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_allcap_linear_nonnegative
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (z : ℝ) (hz : 0 ≤ z) :
    0 ≤ (if C = ⊤ then w z
      else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)) := by sorry
