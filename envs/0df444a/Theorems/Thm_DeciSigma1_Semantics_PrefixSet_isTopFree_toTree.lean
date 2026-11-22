-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_PrefixSet_isTopFree_toTree
-- name    : DeciSigma1.Semantics.PrefixSet.isTopFree_toTree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:54:41.018162+00:00
-- url     : https://prove2.me/theorems/1f8e45f1-0854-47a5-968a-6a3f26eb574a
-- title:
--   Prefix Set: is Top Free to Tree
-- statement:
--   The label `⊤` does not occur in an embedded tree.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L155-L158
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L155-L158

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

theorem DeciSigma1.Semantics.PrefixSet.isTopFree_toTree (P : PrefixSet n) : P.toTree.IsTopFree := by sorry
