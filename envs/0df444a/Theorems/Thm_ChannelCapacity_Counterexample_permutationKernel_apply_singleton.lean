-- Prove2me | Theorems.Thm_ChannelCapacity_Counterexample_permutationKernel_apply_singleton
-- name    : ChannelCapacity.Counterexample.permutationKernel_apply_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:42.412234+00:00
-- url     : https://prove2.me/theorems/ca401bb6-f397-4c69-bf18-685138cfec0b
-- title:
--   Counterexample: permutation Kernel apply singleton
-- statement:
--   The Counterexample construction uses the permutation Kernel apply singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Counterexample.lean#L155-L157
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Counterexample.lean#L155-L157

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

theorem ChannelCapacity.Counterexample.permutationKernel_apply_singleton (i : Fin 6) (y : Fin 3) :
    permutationKernel i {y} = rowPMF i y := by sorry
