-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_upperSemicontinuous_mutualInformation
-- name    : ChannelCapacity.Kernel.ContinuousPositiveDensity.upperSemicontinuous_mutualInformation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:18.982399+00:00
-- url     : https://prove2.me/theorems/ace1e419-a884-4f1a-9914-e824c9b50654
-- title:
--   Continuous Positive Density: upper Semicontinuous mutual Information
-- statement:
--   The Continuous Positive Density construction uses the upper Semicontinuous mutual Information property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L89-L92
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L89-L92

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

theorem ChannelCapacity.Kernel.ContinuousPositiveDensity.upperSemicontinuous_mutualInformation
    (h : ContinuousPositiveDensity k ν) :
    UpperSemicontinuous fun p : ProbabilityMeasure α => mutualInformation p k := by sorry
