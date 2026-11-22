-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_FiniteMedian_median_of_f
-- name    : DeciSigma1.Semantics.FiniteMedian.median_of_f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:04:10.026797+00:00
-- url     : https://prove2.me/theorems/1f80ee3d-a980-4a8f-98ec-4f3165cf97e2
-- title:
--   Finite Median: median of f
-- statement:
--   The Finite Median construction uses the median of f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/FiniteMedian.lean#L102-L105
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/FiniteMedian.lean#L102-L105

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

theorem DeciSigma1.Semantics.FiniteMedian.median_of_f {a b c : FTree n}
    (h : medianSym (rootLabel a) (rootLabel b) (rootLabel c) = .f) :
    median a b c = .node fun i => median (child a i) (child b i) (child c i) := by sorry
