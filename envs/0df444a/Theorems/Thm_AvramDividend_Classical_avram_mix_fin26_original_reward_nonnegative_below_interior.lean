-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_reward_nonnegative_below_interior
-- name    : AvramDividend.Classical.avram_mix_fin26_original_reward_nonnegative_below_interior
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:57:32.134031+00:00
-- url     : https://prove2.me/theorems/29c0a475-0cd9-40c0-8fbe-d375aeb5b4e4
-- title:
--   Original finite-mixed reward nonnegative at all negative-jump landing reserves below an interior cap
-- statement:
--   Under the original reward boundary, continuity, C2 smoothness and gradient >= 1 up to the admissible cap, all reward evaluations at real reserves t below any strictly interior positive reserve v are nonnegative. For t<0 use the negative-side zero extension; at t=0 use w(0)>=0; for 0<t<=v use the previously Proved closed-cap positive-initial reward theorem and monotonicity of ENNReal.ofReal. This supplies the full negative-mark landing hypothesis of the finite-activity generator lower estimate on compact interior intervals.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin22_positive_initial_from_closed_cap_gradient
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin26_original_reward_nonnegative_below_interior
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (v : ℝ) (hv : 0 < v) (hvC : ENNReal.ofReal v < C) :
    ∀ t : ℝ, t ≤ v → 0 ≤ w t := by sorry
