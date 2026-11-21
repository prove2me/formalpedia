-- Prove2me | Theorems.Thm_ChannelCapacity_continuous_conditionalEntropy
-- name    : ChannelCapacity.continuous_conditionalEntropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:13.314462+00:00
-- url     : https://prove2.me/theorems/9cf88ea4-6696-420b-b193-67f61ff2ac3a
-- title:
--   Channel Capacity: continuous conditional Entropy
-- statement:
--   The Channel Capacity construction uses the continuous conditional Entropy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L578-L582
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L578-L582

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
omit [MeasurableSingletonClass β] [TopologicalSpace β] [DiscreteTopology β] [BorelSpace β]
  [CompactSpace β]

theorem ChannelCapacity.continuous_conditionalEntropy (k : Kernel α β) [IsMarkovKernel k] :
    Continuous fun p : ProbabilityMeasure α => conditionalEntropy p k := by sorry
