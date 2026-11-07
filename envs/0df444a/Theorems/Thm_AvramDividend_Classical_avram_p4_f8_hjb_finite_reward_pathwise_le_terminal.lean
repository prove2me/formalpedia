-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f8_hjb_finite_reward_pathwise_le_terminal
-- name    : AvramDividend.Classical.avram_p4_f8_hjb_finite_reward_pathwise_le_terminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:20:12.858215+00:00
-- url     : https://prove2.me/theorems/4c837c02-2de7-4b89-afda-f848d3a313e8
-- title:
--   Original killed upper-exit reward bounded pointwise by stopped terminal reward
-- statement:
--   On the successful finite corrected upper-before-lower upcross event, the stopped original process contacts the upper barrier exactly, so the discounted reward agrees with the terminal test function; outside that event the nonnegative stopped test payoff dominates zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f8_hjb_finite_reward_pathwise_le_terminal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hTop : C = ⊤)
    (q : ℝ) (hq : 0 < q)
    (b : ℝ) (n : ℕ) (hb : 1 ≤ b) (ω : Ω) :
    (if twoSidedExitUpTimeCorrected X (b - 1) ω < twoSidedExitDownTimeCorrected X (-1) ω ∧ twoSidedExitUpTimeCorrected X (b - 1) ω ≤ (n : ℝ≥0∞) then ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTimeCorrected X (b - 1) ω))) * w b) else 0) ≤
    ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (min (twoSidedExitUpTimeCorrected X (b - 1) ω) (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))))) * w (1 + X.X (ENNReal.toNNReal (min (twoSidedExitUpTimeCorrected X (b - 1) ω) (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞)))) ω)) := by sorry
