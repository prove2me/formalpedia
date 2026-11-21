-- Prove2me | Theorems.Thm_ChannelCapacity_continuous_outputPrior
-- name    : ChannelCapacity.continuous_outputPrior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:37.988181+00:00
-- url     : https://prove2.me/theorems/d46d85aa-ca2e-46e9-8c9a-84f1ec274e51
-- title:
--   Channel Capacity: continuous output Prior
-- statement:
--   The Channel Capacity construction uses the continuous output Prior property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L553-L566
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L553-L566

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
omit [Fintype α] [Fintype β] [DiscreteTopology β]

theorem ChannelCapacity.continuous_outputPrior [Finite α] [Finite β] (k : Kernel α β) [IsMarkovKernel k] :
    Continuous fun p : ProbabilityMeasure α => outputPrior k p := by sorry
