-- Prove2me | Theorems.Thm_ChannelCapacity_toReal_klDiv_count
-- name    : ChannelCapacity.toReal_klDiv_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:23.455392+00:00
-- url     : https://prove2.me/theorems/a88b9d07-5633-4014-81e2-62e55338dc3e
-- title:
--   Channel Capacity: to Real kl Div count
-- statement:
--   The Channel Capacity construction uses the to Real kl Div count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L86-L112
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L86-L112

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

theorem ChannelCapacity.toReal_klDiv_count (μ : ProbabilityMeasure α) :
    (InformationTheory.klDiv μ.toMeasure Measure.count).toReal =
      (Fintype.card α : ℝ) - 1 - ProbabilityMeasure.entropy μ := by sorry
