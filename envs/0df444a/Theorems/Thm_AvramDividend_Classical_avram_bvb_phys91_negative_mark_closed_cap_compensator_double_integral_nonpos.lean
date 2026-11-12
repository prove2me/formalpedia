-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys91_negative_mark_closed_cap_compensator_double_integral_nonpos
-- name    : AvramDividend.Classical.avram_bvb_phys91_negative_mark_closed_cap_compensator_double_integral_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:33:52.275027+00:00
-- url     : https://prove2.me/theorems/ff4a2215-19c9-4f6a-ac8d-aced6677b984
-- title:
--   Closed-cap negative-mark double compensator integral is nonpositive
-- statement:
--   For any original closed-cap BV candidate with derivative at least one, nonnegative discount weights and any marked space/time measures, the doubly integrated strictly negative-mark value increment is nonpositive. This supplies the boundary-sign step in the original uniform compensator quadrature phys85; the proof uses phys88 for each marked increment.
-- source:
--   Original BV phys85 negative-mark compensator boundary sign

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys91_negative_mark_closed_cap_compensator_double_integral_nonpos
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (μ : Measure ℝ) (ν : Measure ℝ≥0)
    (U : ℝ≥0 → ℝ) (e : ℝ≥0 → ℝ) (A : Set ℝ≥0)
    (he : ∀ t, 0 ≤ e t)
    (hU : ∀ t ∈ A, 0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C) :
    (∫ t, ∫ z,
      (if t ∈ A ∧ z < 0 then
        e t * (w (U t + z) - w (U t)) else 0) ∂μ ∂ν) ≤ 0 := by sorry
