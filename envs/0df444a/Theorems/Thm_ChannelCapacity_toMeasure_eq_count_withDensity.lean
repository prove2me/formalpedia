-- Prove2me | Theorems.Thm_ChannelCapacity_toMeasure_eq_count_withDensity
-- name    : ChannelCapacity.toMeasure_eq_count_withDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:30.765792+00:00
-- url     : https://prove2.me/theorems/44776b6e-eb49-4c67-88c2-6f6020e88e4c
-- title:
--   Channel Capacity: to Measure eq count with Density
-- statement:
--   The Channel Capacity construction uses the to Measure eq count with Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L57-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L57-L63

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
omit [Fintype α]

theorem ChannelCapacity.toMeasure_eq_count_withDensity (μ : ProbabilityMeasure α) :
    [Countable α] → μ.toMeasure = Measure.count.withDensity (fun a => μ.toMeasure {a}) := by sorry
