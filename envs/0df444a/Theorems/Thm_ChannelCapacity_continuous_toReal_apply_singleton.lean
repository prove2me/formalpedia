-- Prove2me | Theorems.Thm_ChannelCapacity_continuous_toReal_apply_singleton
-- name    : ChannelCapacity.continuous_toReal_apply_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:34.957273+00:00
-- url     : https://prove2.me/theorems/11e087d6-fbed-4269-885b-665841324aa4
-- title:
--   Channel Capacity: continuous to Real apply singleton
-- statement:
--   The Channel Capacity construction uses the continuous to Real apply singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L513-L517
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L513-L517

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
omit [Fintype α]

theorem ChannelCapacity.continuous_toReal_apply_singleton (a : α) :
    Continuous fun p : ProbabilityMeasure α => (p.toMeasure {a}).toReal := by sorry
