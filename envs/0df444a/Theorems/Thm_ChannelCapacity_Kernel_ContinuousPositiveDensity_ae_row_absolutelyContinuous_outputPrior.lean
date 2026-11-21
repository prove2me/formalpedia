-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_ae_row_absolutelyContinuous_outputPrior
-- name    : ChannelCapacity.Kernel.ContinuousPositiveDensity.ae_row_absolutelyContinuous_outputPrior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:40.448667+00:00
-- url     : https://prove2.me/theorems/49c9ef17-a07c-463e-bff5-2264e71c9956
-- title:
--   Continuous Positive Density: ae row absolutely Continuous output Prior
-- statement:
--   The Continuous Positive Density construction uses the ae row absolutely Continuous output Prior property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L192-L204
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L192-L204

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
omit [CompactSpace β] [BorelSpace α] [BorelSpace β]

theorem ChannelCapacity.Kernel.ContinuousPositiveDensity.ae_row_absolutelyContinuous_outputPrior
    (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) :
    ∀ᵐ a ∂p.toMeasure, k a ≪ (outputPrior k p).toMeasure := by sorry
