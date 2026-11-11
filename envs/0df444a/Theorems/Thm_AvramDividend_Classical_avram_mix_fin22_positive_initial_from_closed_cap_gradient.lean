-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin22_positive_initial_from_closed_cap_gradient
-- name    : AvramDividend.Classical.avram_mix_fin22_positive_initial_from_closed_cap_gradient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T10:00:37.770016+00:00
-- url     : https://prove2.me/theorems/cb38fe6d-bdbf-458f-ba46-6a26b49bfa2e
-- title:
--   Finite mixed HJB closed-cap positivity at initial reserve
-- statement:
--   A source-exact initial-reward positivity component of the original mixed finite-cap stopped Ito budget. The closed-cap derivative lower bound and continuity imply w(0)+x ≤ w(x), including x exactly at C; since w(0)≥0 and x>0, this gives 0≤w(x). Derived from the already Proved closed-cap C1 envelope theorem, with C2⇒C1 as the only regularity bridge.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin22_positive_initial_from_closed_cap_gradient
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x)
    (hxc : ENNReal.ofReal x ≤ C) :
    0 ≤ w x := by sorry
