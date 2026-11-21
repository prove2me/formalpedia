-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_row_eq_withDensity
-- name    : ChannelCapacity.Kernel.ContinuousPositiveDensity.row_eq_withDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:33.400179+00:00
-- url     : https://prove2.me/theorems/19d88ce1-601b-4658-b216-0e8a3080ef02
-- title:
--   Continuous Positive Density: row eq with Density
-- statement:
--   The Continuous Positive Density construction uses the row eq with Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L67-L69
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L67-L69

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

theorem ChannelCapacity.Kernel.ContinuousPositiveDensity.row_eq_withDensity (h : ContinuousPositiveDensity k ν) (a : α) :
    k a = ν.withDensity (fun b => (h.density a b : ENNReal)) := by sorry
