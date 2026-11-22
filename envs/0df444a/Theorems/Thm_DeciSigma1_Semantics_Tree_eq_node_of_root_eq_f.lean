-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_eq_node_of_root_eq_f
-- name    : DeciSigma1.Semantics.Tree.eq_node_of_root_eq_f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:15.213955+00:00
-- url     : https://prove2.me/theorems/b4d7a821-132f-446a-b84e-723fbb88f272
-- title:
--   Tree: eq node of root eq f
-- statement:
--   The Tree construction uses the eq node of root eq f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean#L271-L277
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean#L271-L277

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

theorem DeciSigma1.Semantics.Tree.eq_node_of_root_eq_f (t : Tree n) (h : t.fn [] = some Sym.f) :
    t = node (fun i => t.branch i h) := by sorry
