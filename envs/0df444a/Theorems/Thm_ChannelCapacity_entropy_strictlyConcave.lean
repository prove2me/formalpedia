-- Prove2me | Theorems.Thm_ChannelCapacity_entropy_strictlyConcave
-- name    : ChannelCapacity.entropy_strictlyConcave
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:17.190682+00:00
-- url     : https://prove2.me/theorems/02370cf7-5dd7-4ba9-ba9f-1be8d2da07d6
-- title:
--   Channel Capacity: entropy strictly Concave
-- statement:
--   The Channel Capacity construction uses the entropy strictly Concave property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L375-L427
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L375-L427

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

theorem ChannelCapacity.entropy_strictlyConcave (p q : ProbabilityMeasure α) (h_ne : p ≠ q)
    (t : NNReal) (ht_pos : 0 < t) (ht_lt_one : t < 1) :
    ProbabilityMeasure.entropy (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) >
      (t : ℝ) * ProbabilityMeasure.entropy p + (1 - (t : ℝ)) * ProbabilityMeasure.entropy q := by sorry
