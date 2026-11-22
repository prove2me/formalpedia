-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_PrefixSet_toTree_fn_eq_f
-- name    : DeciSigma1.Semantics.PrefixSet.toTree_fn_eq_f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:55:08.192538+00:00
-- url     : https://prove2.me/theorems/1aa079ae-92df-4e4e-8d23-b775b306f30a
-- title:
--   Prefix Set: to Tree fn eq f
-- statement:
--   The Prefix Set construction uses the to Tree fn eq f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L149-L152
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L149-L152

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

theorem DeciSigma1.Semantics.PrefixSet.toTree_fn_eq_f (P : PrefixSet n) (π : List (Fin n)) :
    P.toTree.fn π = some Sym.f ↔ π ∈ P.carrier := by sorry
