-- Prove2me | Theorems.Thm_ChannelCapacity_continuous_mutualInformation_of_finite
-- name    : ChannelCapacity.continuous_mutualInformation_of_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:41.9175+00:00
-- url     : https://prove2.me/theorems/a5067183-e624-4cbd-b9ba-5f69e668cac3
-- title:
--   Channel Capacity: continuous mutual Information of finite
-- statement:
--   The Channel Capacity construction uses the continuous mutual Information of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L586-L593
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L586-L593

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
open ChannelCapacity
variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
variable [TopologicalSpace α] [TopologicalSpace β]
  [DiscreteTopology α] [DiscreteTopology β]
  [BorelSpace α] [BorelSpace β]
  [CompactSpace α] [CompactSpace β]
omit [Fintype α] [Fintype β] [TopologicalSpace β] [DiscreteTopology β] [BorelSpace β]
  [CompactSpace β]

theorem ChannelCapacity.continuous_mutualInformation_of_finite [Finite α] [Finite β]
    (k : Kernel α β) [IsMarkovKernel k] :
    Continuous fun p : ProbabilityMeasure α => mutualInformation p k := by sorry
