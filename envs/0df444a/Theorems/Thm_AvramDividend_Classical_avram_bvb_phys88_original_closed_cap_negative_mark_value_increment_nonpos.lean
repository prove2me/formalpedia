-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys88_original_closed_cap_negative_mark_value_increment_nonpos
-- name    : AvramDividend.Classical.avram_bvb_phys88_original_closed_cap_negative_mark_value_increment_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:22:16.485309+00:00
-- url     : https://prove2.me/theorems/ff6949ca-12c9-4214-8800-7e31a6d2a0e3
-- title:
--   Original closed-cap negative jump mark has nonpositive candidate increment
-- statement:
--   For the BV verification candidate, every strictly negative jump mark at any nonnegative pre-jump reserve up to the closed cap has nonpositive w-increment, even if the jump overshoots below zero. This follows from the previously Proved closed-cap two-point gradient envelope and nonnegativity at zero. It supplies the sign of omitted cap/zero boundary contributions in the compensator quadrature phys85.
-- source:
--   Boundary-sign lemma for phys85 original zero-mark generator compensation; reuses proved aeec073e

import Mathlib
open Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys88_original_closed_cap_negative_mark_value_increment_nonpos
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (b z : ℝ) (hb : 0 ≤ b) (hbC : ENNReal.ofReal b ≤ C)
    (hz : z < 0) :
    w (b + z) - w b ≤ 0  := by sorry
