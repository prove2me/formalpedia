-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_wellConditionedForCapacity_of_continuousPositiveDensity
-- name    : ChannelCapacity.Kernel.ContinuousPositiveDensity.wellConditionedForCapacity_of_continuousPositiveDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:25.91418+00:00
-- url     : https://prove2.me/theorems/f9cedb29-e979-4457-8666-27bfb82c9919
-- title:
--   Continuous Positive Density: well Conditioned For Capacity of continuous Positive Density
-- statement:
--   The Continuous Positive Density construction uses the well Conditioned For Capacity of continuous Positive Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L380-L386
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L380-L386

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

theorem ChannelCapacity.Kernel.ContinuousPositiveDensity.wellConditionedForCapacity_of_continuousPositiveDensity
    (h : ContinuousPositiveDensity k ν) :
    Kernel.WellConditionedForCapacity k := by sorry
