-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_FiniteMedian_extendedLabel_toTree_cons
-- name    : DeciSigma1.Semantics.FiniteMedian.extendedLabel_toTree_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:04:12.163461+00:00
-- url     : https://prove2.me/theorems/8bbd18df-74c7-47f3-ae84-36a1e0fb26bf
-- title:
--   Finite Median: extended Label to Tree cons
-- statement:
--   The Finite Median construction uses the extended Label to Tree cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/FiniteMedian.lean#L111-L113
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/FiniteMedian.lean#L111-L113

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Median
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_FiniteMedian
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics DeciSigma1.Semantics.FiniteMedian
open DeciSigma1.Semantics.Tree
variable {n : ℕ}

theorem DeciSigma1.Semantics.FiniteMedian.extendedLabel_toTree_cons (t : FTree n) (i : Fin n) (w : List (Fin n)) :
    extendedLabel t.toTree (i :: w) = extendedLabel (child t i).toTree w := by sorry
