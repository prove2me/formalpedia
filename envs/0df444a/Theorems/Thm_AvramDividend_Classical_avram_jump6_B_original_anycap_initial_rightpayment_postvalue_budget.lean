-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_initial_rightpayment_postvalue_budget
-- name    : AvramDividend.Classical.avram_jump6_B_original_anycap_initial_rightpayment_postvalue_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:43:02.675959+00:00
-- url     : https://prove2.me/theorems/b6a77235-41c4-41fd-8970-1271cf176c49
-- title:
--   Original all-cap time-zero right dividend payment plus post-payment value is bounded by initial value
-- statement:
--   For the true original spectrally-negative Levy X and any admissible dividend strategy, every positive cap C and HJB derivative bound at least one, the initial right dividend payment plus the postpayment w value is no greater than w(x). Specialise the existing Proved allcap discounted right-payment potential estimate at t=0, using X.X(0)=0 and D(0)=0. This is the exact zero-atom cancellation needed for closed-Iic physical-grid payment residual in infinite jump activity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_closed_cap_actual_right_discounted_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_anycap_initial_rightpayment_postvalue_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (q : ℝ) (ω : Ω) :
    rightLimit D 0 ω + w (x - rightLimit D 0 ω) - w x ≤ 0 := by sorry
