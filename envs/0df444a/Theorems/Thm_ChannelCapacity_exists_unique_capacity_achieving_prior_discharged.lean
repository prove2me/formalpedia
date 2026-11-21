-- Prove2me | Theorems.Thm_ChannelCapacity_exists_unique_capacity_achieving_prior_discharged
-- name    : ChannelCapacity.exists_unique_capacity_achieving_prior_discharged
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:30.53955+00:00
-- url     : https://prove2.me/theorems/2bb116fa-f151-4658-bbfb-cd6d122f68d0
-- title:
--   Channel Capacity: exists unique capacity achieving prior discharged
-- statement:
--   The Channel Capacity construction uses the exists unique capacity achieving prior discharged property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L419-L430
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean#L419-L430

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
variable [CompactSpace α] [CompactSpace β] [PolishSpace α] [PolishSpace β]
variable [BorelSpace α] [BorelSpace β]
variable [OpensMeasurableSpace α] [OpensMeasurableSpace β]
variable [MeasurableSpace.CountableOrCountablyGenerated α β]
variable [Nonempty α]

theorem ChannelCapacity.exists_unique_capacity_achieving_prior_discharged
    (k : Kernel α β) [IsMarkovKernel k]
    (ν : Measure β) [IsFiniteMeasure ν]
    (hDensity : Kernel.ContinuousPositiveDensity k ν)
    (hInj : Kernel.InjectivePriorPushforward k) :
    ∃! p : ProbabilityMeasure α, mutualInformation p k = channelCapacity k := by sorry
