-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_univ_nonempty_probabilityMeasure
-- name    : ChannelCapacity.Kernel.ContinuousPositiveDensity.univ_nonempty_probabilityMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:27.496837+00:00
-- url     : https://prove2.me/theorems/b859839e-c8c1-4456-9292-cf049a5b73a5
-- title:
--   Continuous Positive Density: univ nonempty probability Measure
-- statement:
--   The Continuous Positive Density construction uses the univ nonempty probability Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L396-L398
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L396-L398

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
variable [CompactSpace α] [PolishSpace α] [BorelSpace α] [Nonempty α]
omit [TopologicalSpace α] [CompactSpace α] [PolishSpace α] [BorelSpace α]
  [OpensMeasurableSpace α]

theorem ChannelCapacity.Kernel.ContinuousPositiveDensity.univ_nonempty_probabilityMeasure :
    (Set.univ : Set (ProbabilityMeasure α)).Nonempty := by sorry
