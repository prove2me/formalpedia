-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_node
-- name    : DeciSigma1.Semantics.FTree.toTree_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:33:10.823938+00:00
-- url     : https://prove2.me/theorems/8d309349-a062-49b9-8275-586a792ea24f
-- title:
--   FTree: to Tree node
-- statement:
--   The FTree construction uses the to Tree node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean#L444-L445
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean#L444-L445

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

theorem DeciSigma1.Semantics.FTree.toTree_node (a : Fin n → FTree n) :
    toTree (node a) = Tree.node (fun i => toTree (a i)) := by sorry

attribute [defeq] DeciSigma1.Semantics.FTree.toTree_node
