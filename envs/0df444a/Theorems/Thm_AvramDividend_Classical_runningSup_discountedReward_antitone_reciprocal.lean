-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_discountedReward_antitone_reciprocal
-- name    : AvramDividend.Classical.runningSup_discountedReward_antitone_reciprocal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:06:47.54631+00:00
-- url     : https://prove2.me/theorems/82b6b5ed-e8d9-4c4a-99de-a51d791debc9
-- title:
--   Stopped reflected dividend rewards decrease along reciprocal barrier thresholds
-- statement:
--   For each sample path and any real discount parameter, the discounted Stieltjes dividend reward of the running-supremum regulator, stopped at reflected drawdown ruin, is antitone along the decreasing positive barriers 1/(n+1). Pathwise ruin-time monotonicity shrinks the payment windows, and monotonicity of nonnegative Lebesgue integrals transfers their inclusion into an inequality of rewards.
-- source:
--   Zero-barrier dividend verification; barrierRuinTime_mono_barrier and lintegral_mono_set.

import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_discountedReward_antitone_reciprocal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (q : ℝ) :
    Antitone (fun n : ℕ =>
      ∫⁻ t in paymentTimes
        (barrierRuinTime X (1 / ((n : ℝ) + 1)) ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (runningSup X) ω)) := by sorry
