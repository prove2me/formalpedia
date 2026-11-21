-- Prove2me | Theorems.Thm_ChannelCapacity_toReal_joint_klDiv_count
-- name    : ChannelCapacity.toReal_joint_klDiv_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:09.86505+00:00
-- url     : https://prove2.me/theorems/9710dab2-73e3-40bb-8c24-72988cbd74cb
-- title:
--   Channel Capacity: to Real joint kl Div count
-- statement:
--   The Channel Capacity construction uses the to Real joint kl Div count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L279-L313
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean#L279-L313

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
omit [Fintype β]

theorem ChannelCapacity.toReal_joint_klDiv_count (k : Kernel α β) [IsMarkovKernel k] [Finite β]
    (p : ProbabilityMeasure α) :
    (InformationTheory.klDiv
        (jointLaw k p).toMeasure
        (p.toMeasure ⊗ₘ Kernel.const α Measure.count)).toReal =
      ∑ a, (p.toMeasure {a}).toReal *
        (InformationTheory.klDiv (k a) Measure.count).toReal := by sorry
