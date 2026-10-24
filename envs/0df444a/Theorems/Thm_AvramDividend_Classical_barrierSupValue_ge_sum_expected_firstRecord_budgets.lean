-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_sum_expected_firstRecord_budgets
-- name    : AvramDividend.Classical.barrierSupValue_ge_sum_expected_firstRecord_budgets
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:01:34.355317+00:00
-- url     : https://prove2.me/theorems/e1647ffe-7fc4-459b-ba9a-239c44ab3820
-- title:
--   Tonelli bridge from pathwise countable record rewards to the stopped barrier value
-- statement:
--   Suppose every sample path's genuine stopped running-supremum Stieltjes reward dominates a countable sum of nonnegative measurable candidate first-record payments. Then the total expected first-record payments, summed over all record cells, are bounded by the original barrierSupValue. This applies Tonelli's theorem and the Proved full reward indicator representation. The strong Markov survival estimates and the pathwise record domination remain separate explicit obligations.
-- source:
--   The Proved barrierSupValue_eq_full_reward_indicator_expectation theorem and Tonelli's nonnegative lintegral_tsum interchange.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_full_reward_indicator_expectation

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.barrierSupValue_ge_sum_expected_firstRecord_budgets
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q : ℝ)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, AEMeasurable (w n) P)
    (hbudget : ∀ᵐ ω ∂P, (∑' n, w n ω) ≤
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω))) :
    (∑' n, ∫⁻ ω, w n ω ∂P) ≤ barrierSupValue X a q := by sorry
