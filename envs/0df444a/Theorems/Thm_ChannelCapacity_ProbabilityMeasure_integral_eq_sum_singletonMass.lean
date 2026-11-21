-- Prove2me | Theorems.Thm_ChannelCapacity_ProbabilityMeasure_integral_eq_sum_singletonMass
-- name    : ChannelCapacity.ProbabilityMeasure.integral_eq_sum_singletonMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:12.451148+00:00
-- url     : https://prove2.me/theorems/e4129bb4-0c56-474d-9b7b-79683abb3941
-- title:
--   Probability Measure: integral eq sum singleton Mass
-- statement:
--   The Probability Measure construction uses the integral eq sum singleton Mass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L526-L535
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L526-L535

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
variable [TopologicalSpace α] [TopologicalSpace β]
  [DiscreteTopology α] [DiscreteTopology β]
  [BorelSpace α] [BorelSpace β]
  [CompactSpace α] [CompactSpace β]
omit [TopologicalSpace α] [DiscreteTopology α] [BorelSpace α] [CompactSpace α]

theorem ChannelCapacity.ProbabilityMeasure.integral_eq_sum_singletonMass (μ : ProbabilityMeasure α) (f : α → ℝ) :
    ∫ a, f a ∂μ.toMeasure = ∑ a, (μ.toMeasure {a}).toReal * f a := by sorry
