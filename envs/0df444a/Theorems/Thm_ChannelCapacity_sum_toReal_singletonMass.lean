-- Prove2me | Theorems.Thm_ChannelCapacity_sum_toReal_singletonMass
-- name    : ChannelCapacity.sum_toReal_singletonMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:53.167674+00:00
-- url     : https://prove2.me/theorems/389967ae-72b1-4dc2-b313-4f55b3d47bde
-- title:
--   Channel Capacity: sum to Real singleton Mass
-- statement:
--   The Channel Capacity construction uses the sum to Real singleton Mass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L114-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L114-L126

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

theorem ChannelCapacity.sum_toReal_singletonMass (μ : ProbabilityMeasure α) :
    ∑ a, (μ.toMeasure {a}).toReal = 1 := by sorry
