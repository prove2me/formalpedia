-- Prove2me | Theorems.Thm_ChannelCapacity_klDiv_count_ne_top
-- name    : ChannelCapacity.klDiv_count_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:26.573179+00:00
-- url     : https://prove2.me/theorems/88883de6-211c-410b-a219-a97e7806f166
-- title:
--   Channel Capacity: kl Div count ne top
-- statement:
--   The Channel Capacity construction uses the kl Div count ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L243-L250
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L243-L250

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
omit [Fintype β]

theorem ChannelCapacity.klDiv_count_ne_top (μ : ProbabilityMeasure β) [Finite β] :
    InformationTheory.klDiv μ.toMeasure Measure.count ≠ ∞ := by sorry
