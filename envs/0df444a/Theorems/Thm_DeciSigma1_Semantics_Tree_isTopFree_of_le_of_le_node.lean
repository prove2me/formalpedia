-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_isTopFree_of_le_of_le_node
-- name    : DeciSigma1.Semantics.Tree.isTopFree_of_le_of_le_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:58:45.144715+00:00
-- url     : https://prove2.me/theorems/1a278e1a-678a-437d-aa37-e12adb2a8b23
-- title:
--   Tree: is Top Free of le of le node
-- statement:
--   If `u ≤ f(u, …, u)` in the covariant order, then `⊤` does not occur in any tree below
--   `u`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L106-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L106-L120

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
open DeciSigma1.Semantics.Tree

theorem DeciSigma1.Semantics.Tree.isTopFree_of_le_of_le_node {t u : Tree n} (hu : u ≤ node fun _ => u) (ht : t ≤ u) :
    t.IsTopFree := by sorry
