-- Prove2me | Theorems.Thm_ChannelCapacity_outputPrior_apply_singleton
-- name    : ChannelCapacity.outputPrior_apply_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:00.566887+00:00
-- url     : https://prove2.me/theorems/6c2e86de-29ca-4c9d-b5d7-13dc4297ca4c
-- title:
--   Channel Capacity: output Prior apply singleton
-- statement:
--   The Channel Capacity construction uses the output Prior apply singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L217-L229
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L217-L229

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

theorem ChannelCapacity.outputPrior_apply_singleton (k : Kernel α β) [IsMarkovKernel k]
    (p : ProbabilityMeasure α) (b : β) :
    (outputPrior k p).toMeasure {b} = ∑ a, p.toMeasure {a} * k a {b} := by sorry
