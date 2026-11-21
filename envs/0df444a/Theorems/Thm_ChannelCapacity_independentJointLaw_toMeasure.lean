-- Prove2me | Theorems.Thm_ChannelCapacity_independentJointLaw_toMeasure
-- name    : ChannelCapacity.independentJointLaw_toMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:38.760208+00:00
-- url     : https://prove2.me/theorems/2ffed862-0bca-4cb8-9084-7eeb6255af44
-- title:
--   Channel Capacity: independent Joint Law to Measure
-- statement:
--   The Channel Capacity construction uses the independent Joint Law to Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Basic.lean#L113-L117
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Basic.lean#L113-L117

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

theorem ChannelCapacity.independentJointLaw_toMeasure (k : Kernel α β) [IsMarkovKernel k]
    (p : ProbabilityMeasure α) :
    (independentJointLaw k p).toMeasure =
      p.toMeasure ⊗ₘ Kernel.const α (outputPrior k p).toMeasure := by sorry

attribute [defeq] ChannelCapacity.independentJointLaw_toMeasure
