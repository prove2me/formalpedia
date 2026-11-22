-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_PrefixSet_toTree_bot
-- name    : DeciSigma1.Semantics.PrefixSet.toTree_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:54:37.275036+00:00
-- url     : https://prove2.me/theorems/5552b70b-274c-4924-843f-138f2f739890
-- title:
--   Prefix Set: to Tree bot
-- statement:
--   The embedding maps `⊥` to `⊥`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L180-L182
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L180-L182

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Mathlib.Data.Set.Finite.List
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Embedding
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_bot
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_bot


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}
open DeciSigma1.Semantics.PrefixSet

theorem DeciSigma1.Semantics.PrefixSet.toTree_bot : (bot : PrefixSet n).toTree = Tree.bot := by sorry
