-- Prove2me | Theorems.Thm_ChannelCapacity_convexCombination_toReal_apply
-- name    : ChannelCapacity.convexCombination_toReal_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:26.299472+00:00
-- url     : https://prove2.me/theorems/de8960ec-66d0-4571-b268-5ad53a118f3c
-- title:
--   Channel Capacity: convex Combination to Real apply
-- statement:
--   The Channel Capacity construction uses the convex Combination to Real apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L182-L198
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L182-L198

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

theorem ChannelCapacity.convexCombination_toReal_apply (p q : ProbabilityMeasure α) (t : NNReal)
    (ht : t ≤ (1 : NNReal)) (a : α) :
    ((ProbabilityMeasure.convexCombination p q t ht).toMeasure {a}).toReal =
      (t : ℝ) * (p.toMeasure {a}).toReal + (1 - (t : ℝ)) * (q.toMeasure {a}).toReal := by sorry
