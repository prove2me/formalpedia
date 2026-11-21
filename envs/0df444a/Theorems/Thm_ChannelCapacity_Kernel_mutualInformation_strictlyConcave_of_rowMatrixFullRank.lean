-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_mutualInformation_strictlyConcave_of_rowMatrixFullRank
-- name    : ChannelCapacity.Kernel.mutualInformation_strictlyConcave_of_rowMatrixFullRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:07.808232+00:00
-- url     : https://prove2.me/theorems/524c531e-a625-41d7-9327-de629912310f
-- title:
--   Kernel: mutual Information strictly Concave of row Matrix Full Rank
-- statement:
--   The Kernel construction uses the mutual Information strictly Concave of row Matrix Full Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L461-L499
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L461-L499

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

theorem ChannelCapacity.Kernel.mutualInformation_strictlyConcave_of_rowMatrixFullRank [Finite β]
    (k : Kernel α β) [IsMarkovKernel k] (hRank : ChannelCapacity.Kernel.RowMatrixFullRank k) :
    ∀ (p q : ProbabilityMeasure α) (_h_ne : p ≠ q) (t : NNReal)
      (_ht_pos : 0 < t) (ht_lt_one : t < 1),
      mutualInformation (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) k >
        (t : ℝ) * mutualInformation p k + (1 - (t : ℝ)) * mutualInformation q k := by sorry
