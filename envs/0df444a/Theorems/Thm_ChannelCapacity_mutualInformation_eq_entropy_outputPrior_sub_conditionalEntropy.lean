-- Prove2me | Theorems.Thm_ChannelCapacity_mutualInformation_eq_entropy_outputPrior_sub_conditionalEntropy
-- name    : ChannelCapacity.mutualInformation_eq_entropy_outputPrior_sub_conditionalEntropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:30.623893+00:00
-- url     : https://prove2.me/theorems/bcb2e618-aa0a-4895-8814-fc6095f5276f
-- title:
--   Channel Capacity: mutual Information eq entropy output Prior sub conditional Entropy
-- statement:
--   The Channel Capacity construction uses the mutual Information eq entropy output Prior sub conditional Entropy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L315-L373
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L315-L373

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

theorem ChannelCapacity.mutualInformation_eq_entropy_outputPrior_sub_conditionalEntropy
    (k : Kernel α β) [IsMarkovKernel k] [Finite β] (p : ProbabilityMeasure α) :
    mutualInformation p k =
      ProbabilityMeasure.entropy (outputPrior k p) - conditionalEntropy p k := by sorry
