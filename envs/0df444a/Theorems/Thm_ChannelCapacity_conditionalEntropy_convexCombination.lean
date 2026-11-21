-- Prove2me | Theorems.Thm_ChannelCapacity_conditionalEntropy_convexCombination
-- name    : ChannelCapacity.conditionalEntropy_convexCombination
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:57.238186+00:00
-- url     : https://prove2.me/theorems/29aac3c7-c429-43ff-a850-529a69c5f4b6
-- title:
--   Channel Capacity: conditional Entropy convex Combination
-- statement:
--   The Channel Capacity construction uses the conditional Entropy convex Combination property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L201-L207
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L201-L207

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
omit [MeasurableSingletonClass β]

theorem ChannelCapacity.conditionalEntropy_convexCombination (p q : ProbabilityMeasure α) (k : Kernel α β)
    [IsMarkovKernel k] (t : NNReal) (ht : t ≤ (1 : NNReal)) :
    conditionalEntropy (ProbabilityMeasure.convexCombination p q t ht) k =
      (t : ℝ) * conditionalEntropy p k + (1 - (t : ℝ)) * conditionalEntropy q k := by sorry
