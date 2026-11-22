-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_PrefixSet_positions_toTree
-- name    : DeciSigma1.Semantics.PrefixSet.positions_toTree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:54:35.452359+00:00
-- url     : https://prove2.me/theorems/9ea2706a-ebc6-48cc-9ef8-213ccb27f867
-- title:
--   Prefix Set: positions to Tree
-- statement:
--   The constructor positions of the embedded tree are the given ones.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L161-L162
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L161-L162

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

theorem DeciSigma1.Semantics.PrefixSet.positions_toTree (P : PrefixSet n) : P.toTree.positions = P := by sorry
