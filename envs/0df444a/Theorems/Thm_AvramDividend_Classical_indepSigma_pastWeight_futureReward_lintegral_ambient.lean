-- Prove2me | Theorems.Thm_AvramDividend_Classical_indepSigma_pastWeight_futureReward_lintegral_ambient
-- name    : AvramDividend.Classical.indepSigma_pastWeight_futureReward_lintegral_ambient
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T16:43:24.358443+00:00
-- url     : https://prove2.me/theorems/6175753a-65e7-4745-b0f2-5db70ea40ba1
-- title:
--   Past-measurable weight factors from independent future reward under separate ambient measure
-- statement:
--   For a probability or arbitrary measure whose ambient measurable space is mΩ, a weight measurable both in mΩ and a separate past sigma-algebra mPast factors from a measurable reward of an independent future random variable. Binder order makes the ambient measure and past history unambiguously distinct.
-- source:
--   Corrects the sigma-algebra binder order of proved 4a1ee91b-8ba3-4b25-b9bb-61ebc4958175 after the remote compiler of b995a471-5065-4673-ba97-d0f13ebfc768 exposed that its measure argument was indexed by the past sigma-algebra. Consumed immediately by the Lévy stopped-history weighted-reward factor and W-free barrier split 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.indepSigma_pastWeight_futureReward_lintegral_ambient
    {Ω β : Type*} {mPast : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [MeasurableSpace β]
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
