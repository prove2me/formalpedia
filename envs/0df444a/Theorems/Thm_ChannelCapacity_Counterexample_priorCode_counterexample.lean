-- Prove2me | Theorems.Thm_ChannelCapacity_Counterexample_priorCode_counterexample
-- name    : ChannelCapacity.Counterexample.priorCode_counterexample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:45.767579+00:00
-- url     : https://prove2.me/theorems/7eec65ce-4adc-48d4-8b04-90e58aa105b3
-- title:
--   Counterexample: prior Code counterexample
-- statement:
--   The Counterexample construction uses the prior Code counterexample property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Counterexample.lean#L236-L247
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Counterexample.lean#L236-L247

module
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
public import Definitions.Def_LeanPool_ChannelCapacity_Counterexample
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal NNReal
open ChannelCapacity ChannelCapacity.Counterexample

theorem ChannelCapacity.Counterexample.priorCode_counterexample :
    prior₁Code ≠ prior₂Code ∧ outputCode prior₁Code = outputCode prior₂Code := by sorry
