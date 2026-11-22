-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_PrefixSet_toTree_injective
-- name    : DeciSigma1.Semantics.PrefixSet.toTree_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:58:34.052806+00:00
-- url     : https://prove2.me/theorems/63b97ce3-6b28-4225-9307-bca65ff7e4a0
-- title:
--   Prefix Set: to Tree injective
-- statement:
--   The Prefix Set construction uses the to Tree injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L169-L170
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L169-L170

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Mathlib.Data.Set.Finite.List
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Embedding
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}
open DeciSigma1.Semantics.PrefixSet

theorem DeciSigma1.Semantics.PrefixSet.toTree_injective : Function.Injective (toTree (n := n)) := by sorry
