-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_isCompact_univ_probabilityMeasure
-- name    : ChannelCapacity.Kernel.ContinuousPositiveDensity.isCompact_univ_probabilityMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:28.023118+00:00
-- url     : https://prove2.me/theorems/5fafbdb5-5518-47fe-8327-d1264a44e292
-- title:
--   Continuous Positive Density: is Compact univ probability Measure
-- statement:
--   The Continuous Positive Density construction uses the is Compact univ probability Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L401-L403
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L401-L403

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
omit [Nonempty α]

theorem ChannelCapacity.Kernel.ContinuousPositiveDensity.isCompact_univ_probabilityMeasure :
    IsCompact (Set.univ : Set (ProbabilityMeasure α)) := by sorry
