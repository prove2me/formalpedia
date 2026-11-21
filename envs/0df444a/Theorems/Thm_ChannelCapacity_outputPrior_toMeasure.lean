-- Prove2me | Theorems.Thm_ChannelCapacity_outputPrior_toMeasure
-- name    : ChannelCapacity.outputPrior_toMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:35.645219+00:00
-- url     : https://prove2.me/theorems/4ff9bbe1-6b82-4490-a148-0d322e229df2
-- title:
--   Channel Capacity: output Prior to Measure
-- statement:
--   The Channel Capacity construction uses the output Prior to Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Basic.lean#L92-L94
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Basic.lean#L92-L94

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

theorem ChannelCapacity.outputPrior_toMeasure (k : Kernel α β) [IsMarkovKernel k] (p : ProbabilityMeasure α) :
    (outputPrior k p).toMeasure = k ∘ₘ p.toMeasure := by sorry

attribute [defeq] ChannelCapacity.outputPrior_toMeasure
