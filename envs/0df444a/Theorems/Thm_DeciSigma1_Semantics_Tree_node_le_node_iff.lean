-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_node_le_node_iff
-- name    : DeciSigma1.Semantics.Tree.node_le_node_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:33:14.811436+00:00
-- url     : https://prove2.me/theorems/2b2737ac-3d77-4add-9c8e-5be6c59abc87
-- title:
--   Tree: node le node iff
-- statement:
--   The Tree construction uses the node le node iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean#L394-L402
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean#L394-L402

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
open DeciSigma1.Semantics.Tree
variable {n : ℕ}

theorem DeciSigma1.Semantics.Tree.node_le_node_iff (a b : Fin n → Tree n) :
    node a ≤ node b ↔ ∀ i, a i ≤ b i := by sorry
