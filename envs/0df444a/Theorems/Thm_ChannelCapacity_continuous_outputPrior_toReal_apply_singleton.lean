-- Prove2me | Theorems.Thm_ChannelCapacity_continuous_outputPrior_toReal_apply_singleton
-- name    : ChannelCapacity.continuous_outputPrior_toReal_apply_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:34.290355+00:00
-- url     : https://prove2.me/theorems/2c72a203-0e41-45d7-8765-e2098ba46c90
-- title:
--   Channel Capacity: continuous output Prior to Real apply singleton
-- statement:
--   The Channel Capacity construction uses the continuous output Prior to Real apply singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L539-L550
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L539-L550

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

theorem ChannelCapacity.continuous_outputPrior_toReal_apply_singleton [Finite α]
    (k : Kernel α β) [IsMarkovKernel k] (b : β) :
    Continuous fun p : ProbabilityMeasure α => ((outputPrior k p).toMeasure {b}).toReal := by sorry
