-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_mutualInformation_strictlyConcave_of_injectivePriorPushforward
-- name    : ChannelCapacity.Kernel.mutualInformation_strictlyConcave_of_injectivePriorPushforward
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:34.306625+00:00
-- url     : https://prove2.me/theorems/66de6365-10d7-4f35-9313-d7b4c63642df
-- title:
--   Kernel: mutual Information strictly Concave of injective Prior Pushforward
-- statement:
--   The Kernel construction uses the mutual Information strictly Concave of injective Prior Pushforward property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/StrictConcavity.lean#L340-L351
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/StrictConcavity.lean#L340-L351

module
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
open ChannelCapacity
open ProbabilityMeasure
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
open ChannelCapacity.Kernel

theorem ChannelCapacity.Kernel.mutualInformation_strictlyConcave_of_injectivePriorPushforward
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (k : Kernel α β) [IsMarkovKernel k]
    (h : Kernel.InjectivePriorPushforward k)
    (hWC : Kernel.WellConditionedForCapacity k) :
    ∀ (p q : ProbabilityMeasure α) (_h_ne : p ≠ q) (t : NNReal)
      (_ht_pos : 0 < t) (ht_lt_one : t < 1),
      mutualInformation (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) k >
        (t : ℝ) * mutualInformation p k + (1 - (t : ℝ)) * mutualInformation q k := by sorry
