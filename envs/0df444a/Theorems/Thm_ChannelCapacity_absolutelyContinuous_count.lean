-- Prove2me | Theorems.Thm_ChannelCapacity_absolutelyContinuous_count
-- name    : ChannelCapacity.absolutelyContinuous_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:27.219548+00:00
-- url     : https://prove2.me/theorems/45dc8368-2e1a-4a99-bba6-e39ea322e9ed
-- title:
--   Channel Capacity: absolutely Continuous count
-- statement:
--   The Channel Capacity construction uses the absolutely Continuous count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L210-L214
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L210-L214

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
omit [Fintype α] [MeasurableSingletonClass α]

theorem ChannelCapacity.absolutelyContinuous_count (μ : ProbabilityMeasure α) :
    μ.toMeasure ≪ Measure.count := by sorry
