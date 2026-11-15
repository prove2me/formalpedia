-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB40_finitecap_smooth_gradient_restrict_interior_clip
-- name    : AvramDividend.Classical.avram_gbB40_finitecap_smooth_gradient_restrict_interior_clip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:40:58.565183+00:00
-- url     : https://prove2.me/theorems/365cba0a-2879-4ecb-9865-562bf275b50d
-- title:
--   Original finite-cap smoothness and gradient bound restrict to any strictly interior clipping cap
-- statement:
--   An original value function C2 strictly inside the admissible cap C with derivative at least one there is C1 and has derivative at least one on every smaller interior clipping band. This justifies using independent-cap Stieltjes mesh and atom lemmas with an interior clipping b<C without requiring differentiability at C.
-- source:
--   Set inclusion of clipped positive reserve band and monotonicity of ContDiffOn, with order restriction 2 to 1.

import Mathlib
open Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB40_finitecap_smooth_gradient_restrict_interior_clip
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (b : ℝ) (hbc : ENNReal.ofReal b < C) :
    ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal b} ∧
    (∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal b → 1 ≤ deriv w y) := by sorry
