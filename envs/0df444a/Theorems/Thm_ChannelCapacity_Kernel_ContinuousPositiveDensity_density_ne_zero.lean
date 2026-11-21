-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_density_ne_zero
-- name    : ChannelCapacity.Kernel.ContinuousPositiveDensity.density_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:42.135957+00:00
-- url     : https://prove2.me/theorems/68539cba-f152-4ae5-b284-0a40eb992e72
-- title:
--   Continuous Positive Density: density ne zero
-- statement:
--   The Continuous Positive Density construction uses the density ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L77-L79
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L77-L79

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Discharged
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal
open ChannelCapacity
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [TopologicalSpace α] [TopologicalSpace β]
open ChannelCapacity.Kernel
open ChannelCapacity.Kernel.ContinuousPositiveDensity
variable {k : Kernel α β} [IsMarkovKernel k] [OpensMeasurableSpace α] {ν : Measure β}

theorem ChannelCapacity.Kernel.ContinuousPositiveDensity.density_ne_zero (h : ContinuousPositiveDensity k ν) (a : α) (b : β) :
    h.density a b ≠ 0 := by sorry
