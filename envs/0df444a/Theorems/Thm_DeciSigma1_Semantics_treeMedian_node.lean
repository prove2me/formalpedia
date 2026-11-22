-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_treeMedian_node
-- name    : DeciSigma1.Semantics.treeMedian_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:30:59.231834+00:00
-- url     : https://prove2.me/theorems/e089b14b-5953-49e6-8f75-ec8bb07922f8
-- title:
--   Semantics: tree Median node
-- statement:
--   The median commutes with the constructor, child by child.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Median.lean#L214-L220
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Median.lean#L214-L220

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Data.List.Induction
public import Mathlib.Order.MinMax
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.SetLike
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Median
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Semantics.Tree
variable {n : ℕ}

theorem DeciSigma1.Semantics.treeMedian_node (a b c : Fin n → Tree n) :
    treeMedian (Tree.node a) (Tree.node b) (Tree.node c) =
      Tree.node (fun i => treeMedian (a i) (b i) (c i)) := by sorry
