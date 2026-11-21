-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_row_absolutelyContinuous_ref
-- name    : ChannelCapacity.Kernel.ContinuousPositiveDensity.row_absolutelyContinuous_ref
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:44.566002+00:00
-- url     : https://prove2.me/theorems/b4cdd338-1f71-4d93-88e1-14701af8d32a
-- title:
--   Continuous Positive Density: row absolutely Continuous ref
-- statement:
--   The Continuous Positive Density construction uses the row absolutely Continuous ref property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L71-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L71-L75

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

theorem ChannelCapacity.Kernel.ContinuousPositiveDensity.row_absolutelyContinuous_ref (h : ContinuousPositiveDensity k ν) (a : α) :
    k a ≪ ν := by sorry
