-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_FiniteMedian_median_of_top
-- name    : DeciSigma1.Semantics.FiniteMedian.median_of_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:03:57.855849+00:00
-- url     : https://prove2.me/theorems/17805eb7-a7c6-4d49-8495-459dd8492fa3
-- title:
--   Finite Median: median of top
-- statement:
--   The Finite Median construction uses the median of top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/FiniteMedian.lean#L98-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/FiniteMedian.lean#L98-L100

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

theorem DeciSigma1.Semantics.FiniteMedian.median_of_top {a b c : FTree n}
    (h : medianSym (rootLabel a) (rootLabel b) (rootLabel c) = .top) : median a b c = .top := by sorry
