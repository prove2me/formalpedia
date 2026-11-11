-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin27_original_negative_mark_reward_increment_bounded
-- name    : AvramDividend.Classical.avram_mix_fin27_original_negative_mark_reward_increment_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T14:39:46.113742+00:00
-- url     : https://prove2.me/theorems/e8a2fc6a-346f-4447-9ce3-1f18da5ef8ab
-- title:
--   Original mixed finite-activity negative-jump reward increments bounded independently of mark size
-- statement:
--   For a finite-cap mixed source reward w satisfying the original nonnegative left landing, positive-side continuity and HJB gradient hypotheses, any negative jump z from positive reserve y has abs(w(y+z)-w(y)) <= w(y), provided y is strictly inside the cap. Prove monotonicity from the already-Proved positive derivative growth comparison and use original landing reward nonnegativity. This is the precise deterministic bound permitting compensation for arbitrarily large negative marks when negative-jump intensity is finite, without any first absolute moment assumption.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gauss_finitec2_gradient_growth_to_cap
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_reward_nonnegative_below_interior
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin27_original_negative_mark_reward_increment_bounded
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t < 0, w t = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {t : ℝ | 0 < t ∧ ENNReal.ofReal t < C})
    (hw_grad : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t < C → 1 ≤ deriv w t)
    (y z : ℝ) (hy : 0 < y)
    (hyC : ENNReal.ofReal y < C) (hz : z < 0) :
    |w (y + z) - w y| ≤ w y := by sorry
