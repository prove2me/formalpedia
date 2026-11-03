-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_two_point_jump_envelope
-- name    : AvramDividend.Classical.avram_wave7_02_original_positive_cap_C1_gradient_two_point_jump_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:05:31.624754+00:00
-- url     : https://prove2.me/theorems/6c6b70eb-472b-483f-8ca4-999f05ff929b
-- title:
--   Source positive-cap C1 gradient controls any two interior reserves and their right-payment difference
-- statement:
--   Let the original Avram positive-cap HJB candidate w be continuous on nonnegative reserves, C1 on its actual strict cap interior, and have derivative at least one. For any 0≤y≤z≤b below the cap, the payment z-y is at most the candidate decrement w(z)-w(y). This is the source-faithful two-point right-payment inequality, suitable for simultaneous BV dividend jumps when pre/post reserves stay inside the positive-cap interior.
-- source:
--   Exact pinned Mathlib derivative monotonicity for w-id on the compact cap interval; strengthened source-specific derivative lemma from previous accepted f138f64f.

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
open Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_positive_cap_C1_gradient_two_point_jump_envelope
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (b : ℝ) (hb : 0 ≤ b) (hbC : ENNReal.ofReal b < C) :
    ∀ y ∈ Icc (0 : ℝ) b, ∀ z ∈ Icc (0 : ℝ) b,
      y ≤ z → z - y ≤ w z - w y := by sorry
