-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_FiniteMedian_extendedLabel_median
-- name    : DeciSigma1.Semantics.FiniteMedian.extendedLabel_median
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:04:13.358577+00:00
-- url     : https://prove2.me/theorems/9b66d9a6-3208-4219-9810-88e777c13060
-- title:
--   Finite Median: extended Label median
-- statement:
--   The extended labels of the finite median are the medians of the extended labels.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/FiniteMedian.lean#L116-L149
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/FiniteMedian.lean#L116-L149

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

theorem DeciSigma1.Semantics.FiniteMedian.extendedLabel_median (a b c : FTree n) (w : List (Fin n)) :
    extendedLabel (median a b c).toTree w =
      medianSym (extendedLabel a.toTree w) (extendedLabel b.toTree w)
          (extendedLabel c.toTree w) := by sorry
