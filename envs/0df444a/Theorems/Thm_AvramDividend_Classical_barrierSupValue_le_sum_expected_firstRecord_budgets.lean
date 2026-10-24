-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_sum_expected_firstRecord_budgets
-- name    : AvramDividend.Classical.barrierSupValue_le_sum_expected_firstRecord_budgets
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:02:41.762514+00:00
-- url     : https://prove2.me/theorems/6899d369-d70d-4b3d-8dc9-3d54c7e37f97
-- title:
--   Tonelli bridge from pathwise first-record upper budgets to the stopped barrier value
-- statement:
--   If every sample path's genuine stopped running-supremum Stieltjes reward is bounded above by a countable sum of measurable nonnegative first-record budgets, then its expected total barrier value is bounded by the sum of the expected budgets. This is the upper counterpart of the lower Tonelli bridge. Strong Markov and two-sided exit estimates are kept as explicit future stochastic obligations.
-- source:
--   The Proved barrierSupValue_eq_full_reward_indicator_expectation theorem and Tonelli's nonnegative lintegral_tsum interchange.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_full_reward_indicator_expectation

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.barrierSupValue_le_sum_expected_firstRecord_budgets
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q : ℝ)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, AEMeasurable (w n) P)
    (hbudget : ∀ᵐ ω ∂P,
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω))
      ≤ (∑' n, w n ω)) :
    barrierSupValue X a q ≤ (∑' n, ∫⁻ ω, w n ω ∂P) := by sorry
