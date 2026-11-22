-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_PrefixSet_toTree_eq_bot_iff
-- name    : DeciSigma1.Semantics.PrefixSet.toTree_eq_bot_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:54:45.422202+00:00
-- url     : https://prove2.me/theorems/27c1357f-ee1d-423a-8ca3-667f69cf597b
-- title:
--   Prefix Set: to Tree eq bot iff
-- statement:
--   The Prefix Set construction uses the to Tree eq bot iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L198-L199
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L198-L199

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

theorem DeciSigma1.Semantics.PrefixSet.toTree_eq_bot_iff (P : PrefixSet n) : P.toTree = Tree.bot ↔ P = bot := by sorry
