-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_FiniteMedian_median_toTree
-- name    : DeciSigma1.Semantics.FiniteMedian.median_toTree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:03:33.259653+00:00
-- url     : https://prove2.me/theorems/5a4f9324-1675-4f8c-9fe8-936d23f116b3
-- title:
--   Finite Median: median to Tree
-- statement:
--   The finite median represents the median of the corresponding trees.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/FiniteMedian.lean#L152-L156
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/FiniteMedian.lean#L152-L156

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

theorem DeciSigma1.Semantics.FiniteMedian.median_toTree (a b c : FTree n) :
    (median a b c).toTree = treeMedian a.toTree b.toTree c.toTree := by sorry
