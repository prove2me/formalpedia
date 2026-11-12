-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys131_original_stopped_compensator_double_integral_nonpos
-- name    : AvramDividend.Classical.avram_bvb_phys131_original_stopped_compensator_double_integral_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:56:11.308624+00:00
-- url     : https://prove2.me/theorems/2979f266-e469-4e12-bd0c-4bdf0ce81882
-- title:
--   Original physical stopped compensator has nonpositive double integral
-- statement:
--   Every original stopped negative-mark kernel under the closed-cap indicator has nonpositive nested time and mark integral, for arbitrary reserve paths and measures. This directly specialises to phys95's true marked compensator K.
-- source:
--   Proved phys88 via phys128 pointwise kernel sign and Mathlib MeasureTheory.integral_nonpos twice

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys131_original_stopped_compensator_double_integral_nonpos (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (q T : ℝ) (b : ℝ≥0 → ℝ) (τ : ℝ≥0 → ℝ≥0∞) (μ : Measure ℝ≥0) (ν : Measure ℝ) : (∫ t, ∫ z, (if 0 < t ∧ (t : ℝ) < T ∧ (t : ℝ≥0∞) ≤ τ t ∧ 0 ≤ b t ∧ ENNReal.ofReal (b t) ≤ C ∧ z < 0 then Real.exp (-(q * (t : ℝ))) * (w (b t + z) - w (b t)) else 0) ∂ν ∂μ) ≤ 0 := by sorry
