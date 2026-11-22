-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_PrefixSet_finiteTop_toTree_iff
-- name    : DeciSigma1.Semantics.PrefixSet.finiteTop_toTree_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:59:07.65645+00:00
-- url     : https://prove2.me/theorems/3dc9804c-b86f-43a7-a51a-4ec94e6cd889
-- title:
--   Prefix Set: finite Top to Tree iff
-- statement:
--   The embedding preserves and reflects finiteness: `P.toTree` is the tree of a finite term
--   exactly when `P` has finitely many constructor positions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L230-L248
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L230-L248

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

theorem DeciSigma1.Semantics.PrefixSet.finiteTop_toTree_iff (P : PrefixSet n) :
    Full.Models.FiniteTop P.toTree ↔ IsFiniteTree P := by sorry
