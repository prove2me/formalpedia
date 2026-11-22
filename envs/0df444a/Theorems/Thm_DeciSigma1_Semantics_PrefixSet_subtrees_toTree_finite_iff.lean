-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_PrefixSet_subtrees_toTree_finite_iff
-- name    : DeciSigma1.Semantics.PrefixSet.subtrees_toTree_finite_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:58:58.321974+00:00
-- url     : https://prove2.me/theorems/27409f9a-2680-4069-bb3e-cb975bee508a
-- title:
--   Prefix Set: subtrees to Tree finite iff
-- statement:
--   The embedding preserves and reflects regularity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L224-L226
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L224-L226

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

theorem DeciSigma1.Semantics.PrefixSet.subtrees_toTree_finite_iff (P : PrefixSet n) :
    (Characterization.subtrees P.toTree).Finite ↔ IsRegularTree P := by sorry
