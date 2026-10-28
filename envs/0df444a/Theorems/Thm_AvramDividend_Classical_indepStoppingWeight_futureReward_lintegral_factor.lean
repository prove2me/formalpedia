-- Prove2me | Theorems.Thm_AvramDividend_Classical_indepStoppingWeight_futureReward_lintegral_factor
-- name    : AvramDividend.Classical.indepStoppingWeight_futureReward_lintegral_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:51:44.900203+00:00
-- url     : https://prove2.me/theorems/36f318c5-d560-40ee-ac9f-d218736e55b3
-- title:
--   Discounted stopping-time and independent future-path reward factorisation
-- statement:
--   When a finite stopping clock is independent of a measurable future reward path, every measurable nonnegative discount depending on the stopping clock factors from the expected nonnegative future reward. This is the exact weighted-expectation bridge required after strong-Markov independence for first-upcrossing dividend valuation.
-- source:
--   Mathlib.Probability.Independence.Integration via IndepFun.comp and lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun; intended consumer is barrier dividend strong-Markov split 79978d61.

import Mathlib.Probability.Independence.Integration

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.indepStoppingWeight_futureReward_lintegral_factor
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (Y : Ω → β) (hY : Measurable Y)
    (hInd : IndepFun τ Y P)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : β → ℝ≥0∞) (hr : Measurable reward) :
    (∫⁻ ω, discount (τ ω) * reward (Y ω) ∂P) =
      (∫⁻ ω, discount (τ ω) ∂P) *
        (∫⁻ ω, reward (Y ω) ∂P) := by
  sorry
