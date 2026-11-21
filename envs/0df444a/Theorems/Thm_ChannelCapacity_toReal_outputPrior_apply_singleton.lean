-- Prove2me | Theorems.Thm_ChannelCapacity_toReal_outputPrior_apply_singleton
-- name    : ChannelCapacity.toReal_outputPrior_apply_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:37.457426+00:00
-- url     : https://prove2.me/theorems/37e0c70c-09b4-4c70-bc66-ea1a14123967
-- title:
--   Channel Capacity: to Real output Prior apply singleton
-- statement:
--   The Channel Capacity construction uses the to Real output Prior apply singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L232-L240
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L232-L240

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

theorem ChannelCapacity.toReal_outputPrior_apply_singleton (k : Kernel α β) [IsMarkovKernel k]
    (p : ProbabilityMeasure α) (b : β) :
    ((outputPrior k p).toMeasure {b}).toReal =
      ∑ a, (p.toMeasure {a}).toReal * (k a {b}).toReal := by sorry
