-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_outputDensity_pos
-- name    : ChannelCapacity.Kernel.ContinuousPositiveDensity.outputDensity_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:04.414263+00:00
-- url     : https://prove2.me/theorems/8107852a-e103-43a7-8102-530cd57b8482
-- title:
--   Continuous Positive Density: output Density pos
-- statement:
--   The Continuous Positive Density construction uses the output Density pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L169-L189
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L169-L189

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
omit [CompactSpace β] [PolishSpace α] [PolishSpace β] [BorelSpace α] [BorelSpace β]
  [OpensMeasurableSpace β] [IsFiniteMeasure ν]

theorem ChannelCapacity.Kernel.ContinuousPositiveDensity.outputDensity_pos (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) (b : β) :
    0 < h.outputDensity p b := by sorry
