-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_toTree_positions
-- name    : DeciSigma1.Semantics.Tree.toTree_positions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:54:54.810502+00:00
-- url     : https://prove2.me/theorems/c0ea7a84-147a-4f0d-bf14-49ce80dc8a0e
-- title:
--   Tree: to Tree positions
-- statement:
--   A tree without `⊤` is the embedding of its constructor positions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L173-L177
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L173-L177

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

theorem DeciSigma1.Semantics.Tree.toTree_positions {t : Tree n} (ht : t.IsTopFree) :
    t.positions.toTree = t := by sorry
