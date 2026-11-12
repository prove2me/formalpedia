-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys128_original_stopped_compensator_negative_mark_kernel_nonpos
-- name    : AvramDividend.Classical.avram_bvb_phys128_original_stopped_compensator_negative_mark_kernel_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:46:08.644847+00:00
-- url     : https://prove2.me/theorems/f6ad1360-af2f-4e08-a15a-c1044ed7db72
-- title:
--   Original stopped physical compensator kernel has nonpositive sign
-- statement:
--   The original finite-horizon stopped negative-mark compensator kernel with a genuine closed-cap indicator is pointwise nonpositive, including zero and cap contact; this is used to control the omitted boundary contribution in phys95.
-- source:
--   Proved phys88 ff6949ca closed-cap negative-mark jump sign; positive exponential weight

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys88_original_closed_cap_negative_mark_value_increment_nonpos
open Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys128_original_stopped_compensator_negative_mark_kernel_nonpos (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (q T : ℝ) (t : ℝ≥0) (b z : ℝ) (τ : ℝ≥0∞) : (if 0 < t ∧ (t : ℝ) < T ∧ (t : ℝ≥0∞) ≤ τ ∧ 0 ≤ b ∧ ENNReal.ofReal b ≤ C ∧ z < 0 then Real.exp (-(q * (t : ℝ))) * (w (b + z) - w b) else 0) ≤ 0 := by sorry
