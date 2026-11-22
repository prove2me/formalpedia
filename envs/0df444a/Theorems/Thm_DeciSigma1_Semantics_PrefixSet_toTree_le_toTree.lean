-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_PrefixSet_toTree_le_toTree
-- name    : DeciSigma1.Semantics.PrefixSet.toTree_le_toTree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:54:44.49151+00:00
-- url     : https://prove2.me/theorems/2f4e2f3b-440a-449b-8d14-956d503bc97b
-- title:
--   Prefix Set: to Tree le to Tree
-- statement:
--   The embedding preserves and reflects the order.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L165-L167
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L165-L167

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

theorem DeciSigma1.Semantics.PrefixSet.toTree_le_toTree (P Q : PrefixSet n) : P.toTree ≤ Q.toTree ↔ P ≤ Q := by sorry
