-- Prove2me | Theorems.Thm_ChannelCapacity_Counterexample_rowCode_injective
-- name    : ChannelCapacity.Counterexample.rowCode_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:54.477699+00:00
-- url     : https://prove2.me/theorems/72570900-2d97-48ed-886c-c12258c4d059
-- title:
--   Counterexample: row Code injective
-- statement:
--   The Counterexample construction uses the row Code injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Counterexample.lean#L209-L216
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Counterexample.lean#L209-L216

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

theorem ChannelCapacity.Counterexample.rowCode_injective : Function.Injective rowCode := by sorry
