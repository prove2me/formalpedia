-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_PrefixSet_toTree_node
-- name    : DeciSigma1.Semantics.PrefixSet.toTree_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:55:50.716511+00:00
-- url     : https://prove2.me/theorems/42cb717c-2fa6-4589-86ec-5877c4115c1b
-- title:
--   Prefix Set: to Tree node
-- statement:
--   The embedding commutes with the constructor.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L185-L196
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L185-L196

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Mathlib.Data.Set.Finite.List
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Embedding
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_node
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_node


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}
open DeciSigma1.Semantics.PrefixSet

theorem DeciSigma1.Semantics.PrefixSet.toTree_node (a : Fin n → PrefixSet n) :
    (node a).toTree = Tree.node fun i => (a i).toTree := by sorry
