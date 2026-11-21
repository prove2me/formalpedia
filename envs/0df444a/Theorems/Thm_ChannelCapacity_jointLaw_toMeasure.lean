-- Prove2me | Theorems.Thm_ChannelCapacity_jointLaw_toMeasure
-- name    : ChannelCapacity.jointLaw_toMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:46.498499+00:00
-- url     : https://prove2.me/theorems/fb62f317-5dcc-4192-b201-6b4c0ffcd82f
-- title:
--   Channel Capacity: joint Law to Measure
-- statement:
--   The Channel Capacity construction uses the joint Law to Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Basic.lean#L102-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Basic.lean#L102-L104

module
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.Composition.CompNotation
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Basic
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal
open ChannelCapacity
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem ChannelCapacity.jointLaw_toMeasure (k : Kernel α β) [IsMarkovKernel k] (p : ProbabilityMeasure α) :
    (jointLaw k p).toMeasure = p.toMeasure ⊗ₘ k := by sorry

attribute [defeq] ChannelCapacity.jointLaw_toMeasure
