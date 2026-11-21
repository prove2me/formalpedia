-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_aemeasurable_outputDensity
-- name    : ChannelCapacity.Kernel.ContinuousPositiveDensity.aemeasurable_outputDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:35.334182+00:00
-- url     : https://prove2.me/theorems/5c441943-ad03-4164-b359-610f3896ce45
-- title:
--   Continuous Positive Density: aemeasurable output Density
-- statement:
--   The Continuous Positive Density construction uses the aemeasurable output Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L141-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L141-L148

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
variable [CompactSpace α] [CompactSpace β] [PolishSpace α] [PolishSpace β]
variable [BorelSpace α] [BorelSpace β]
variable [OpensMeasurableSpace β] [IsFiniteMeasure ν]
omit [CompactSpace α] [CompactSpace β] [BorelSpace α] [BorelSpace β]

theorem ChannelCapacity.Kernel.ContinuousPositiveDensity.aemeasurable_outputDensity (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) :
    AEMeasurable (h.outputDensity p) ν := by sorry
