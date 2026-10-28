-- Prove2me | Theorems.Thm_AvramDividend_Classical_indepSigma_pastWeight_futureReward_lintegral
-- name    : AvramDividend.Classical.indepSigma_pastWeight_futureReward_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T16:20:14.014629+00:00
-- url     : https://prove2.me/theorems/4a1ee91b-8ba3-4b25-b9bb-61ebc4958175
-- title:
--   Discounted past-history weight factors from an independent future-path reward
-- statement:
--   If a past weight is measurable with respect to a sigma-algebra independent of a future random path, then the expectation of their product factors into the product of expectations. This applies to an indicator of reaching an upper barrier before ruin times the discount at the hitting time, with future dividend reward built from shifted increments.
-- source:
--   Uses Mathlib IndepFun and indep_of_indep_of_le_left, with lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun. Applies to stopped-history independence d5bac6c4-63fd-49ee-a81b-ccda03ccab18 to support strong-Markov barrier-value splitting 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.indepSigma_pastWeight_futureReward_lintegral
    {Ω β : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace β] {mPast : MeasurableSpace Ω}
    (P : Measure Ω)
    (pastWeight : Ω → ℝ≥0∞)
    (hp : Measurable pastWeight)
    (hpPast : Measurable[mPast] pastWeight)
    (Y : Ω → β) (hY : Measurable Y)
    (hInd : Indep mPast (MeasurableSpace.comap Y inferInstance) P)
    (reward : β → ℝ≥0∞) (hr : Measurable reward) :
    (∫⁻ ω, pastWeight ω * reward (Y ω) ∂P) =
      (∫⁻ ω, pastWeight ω ∂P) *
        (∫⁻ ω, reward (Y ω) ∂P) := by
  sorry
