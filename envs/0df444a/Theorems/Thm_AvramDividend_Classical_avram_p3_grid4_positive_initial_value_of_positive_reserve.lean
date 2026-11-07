-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_positive_initial_value_of_positive_reserve
-- name    : AvramDividend.Classical.avram_p3_grid4_positive_initial_value_of_positive_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:37:05.54576+00:00
-- url     : https://prove2.me/theorems/6da04f9a-e389-4e09-a1ed-4ce7df598511
-- title:
--   Original capped C1 HJB candidate has strictly positive benchmark at positive initial reserve
-- statement:
--   The already proved original cap-gradient closed-envelope w(0)+x<=w(x) holds at the positive original initial reserve x with cap membership, including x at finite cap. Since w(0)>=0 and x>0, the source benchmark w(x)>0. This justifies deterministic slack rescaling for all positive reserves, leaving only x=0 to be handled separately.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_positive_initial_value_of_positive_reserve
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Set.Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxpos : 0 < x) (hxc : ENNReal.ofReal x ≤ C) :
    0 < w x := by sorry
