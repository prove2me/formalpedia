-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_outputPrior_eq_withDensity_outputDensity
-- name    : ChannelCapacity.Kernel.ContinuousPositiveDensity.outputPrior_eq_withDensity_outputDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:38.791733+00:00
-- url     : https://prove2.me/theorems/c0a4fe1c-62f9-4e52-bfb6-f98be4b3763d
-- title:
--   Continuous Positive Density: output Prior eq with Density output Density
-- statement:
--   The Continuous Positive Density construction uses the output Prior eq with Density output Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L151-L165
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L151-L165

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

theorem ChannelCapacity.Kernel.ContinuousPositiveDensity.outputPrior_eq_withDensity_outputDensity
    (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) :
    (outputPrior k p).toMeasure = ν.withDensity (h.outputDensity p) := by sorry
