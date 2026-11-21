-- Prove2me | Theorems.Thm_ChannelCapacity_rnDeriv_count_ae
-- name    : ChannelCapacity.rnDeriv_count_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:01.692296+00:00
-- url     : https://prove2.me/theorems/1e4fbf30-aa6e-4bef-b649-7d9cf620135e
-- title:
--   Channel Capacity: rn Deriv count ae
-- statement:
--   The Channel Capacity construction uses the rn Deriv count ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L66-L77
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L66-L77

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

theorem ChannelCapacity.rnDeriv_count_ae (μ : ProbabilityMeasure α) :
    [Countable α] →
      μ.toMeasure.rnDeriv Measure.count =ᵐ[Measure.count] fun a => μ.toMeasure {a} := by sorry
