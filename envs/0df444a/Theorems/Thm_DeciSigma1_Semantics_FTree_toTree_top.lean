-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_top
-- name    : DeciSigma1.Semantics.FTree.toTree_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:33:31.611367+00:00
-- url     : https://prove2.me/theorems/8bbd4eca-6e0b-473c-9e94-8a37ba7ddfae
-- title:
--   FTree: to Tree top
-- statement:
--   The FTree construction uses the to Tree top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean#L443-L443
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean#L443-L443

module
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Order.Lattice
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Semantics.FTree
variable {n : ℕ}

theorem DeciSigma1.Semantics.FTree.toTree_top : toTree (top : FTree n) = Tree.top := by sorry

attribute [defeq] DeciSigma1.Semantics.FTree.toTree_top
