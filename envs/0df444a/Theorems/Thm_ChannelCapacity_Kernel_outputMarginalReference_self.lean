-- Prove2me | Theorems.Thm_ChannelCapacity_Kernel_outputMarginalReference_self
-- name    : ChannelCapacity.Kernel.outputMarginalReference_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:07.735171+00:00
-- url     : https://prove2.me/theorems/ec6081f4-e707-4ad4-be8d-8523e664fe45
-- title:
--   Kernel: output Marginal Reference self
-- statement:
--   The Kernel construction uses the output Marginal Reference self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/NonDegeneracy.lean#L114-L117
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/NonDegeneracy.lean#L114-L117

module
public import Definitions.Def_LeanPool_ChannelCapacity_Basic
public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal
open ChannelCapacity
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
open ChannelCapacity.Kernel

theorem ChannelCapacity.Kernel.outputMarginalReference_self
    (k : Kernel α β) [IsMarkovKernel k] (p : ProbabilityMeasure α) :
    Kernel.OutputMarginalReference k p (outputPrior k p).toMeasure := by sorry
