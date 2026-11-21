-- Prove2me | Theorems.Thm_ChannelCapacity_joint_klDiv_count_ne_top
-- name    : ChannelCapacity.joint_klDiv_count_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:05.198942+00:00
-- url     : https://prove2.me/theorems/c7feff09-8a29-4cfc-bb1c-f20fd8c0d3a9
-- title:
--   Channel Capacity: joint kl Div count ne top
-- statement:
--   The Channel Capacity construction uses the joint kl Div count ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L253-L276
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L253-L276

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
open ChannelCapacity
variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
omit [Fintype α] [Fintype β]

theorem ChannelCapacity.joint_klDiv_count_ne_top (k : Kernel α β) [IsMarkovKernel k] [Finite α] [Finite β]
    (p : ProbabilityMeasure α) :
    InformationTheory.klDiv
        (jointLaw k p).toMeasure
        (p.toMeasure ⊗ₘ Kernel.const α Measure.count) ≠ ∞ := by sorry
