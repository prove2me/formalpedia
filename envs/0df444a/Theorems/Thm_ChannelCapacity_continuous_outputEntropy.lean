-- Prove2me | Theorems.Thm_ChannelCapacity_continuous_outputEntropy
-- name    : ChannelCapacity.continuous_outputEntropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:12.426585+00:00
-- url     : https://prove2.me/theorems/8d85188c-d12c-43b5-bec4-8da9a5009b91
-- title:
--   Channel Capacity: continuous output Entropy
-- statement:
--   The Channel Capacity construction uses the continuous output Entropy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L569-L574
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L569-L574

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
omit [Fintype α] [TopologicalSpace β] [DiscreteTopology β] [BorelSpace β] [CompactSpace β]

theorem ChannelCapacity.continuous_outputEntropy [Finite α] (k : Kernel α β) [IsMarkovKernel k] :
    Continuous fun p : ProbabilityMeasure α => ProbabilityMeasure.entropy (outputPrior k p) := by sorry
