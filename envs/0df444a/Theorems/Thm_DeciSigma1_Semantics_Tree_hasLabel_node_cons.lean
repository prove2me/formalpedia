-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_node_cons
-- name    : DeciSigma1.Semantics.Tree.hasLabel_node_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:31.627022+00:00
-- url     : https://prove2.me/theorems/0985bc4a-4fe1-4434-b8b9-4f6f62c15923
-- title:
--   Tree: has Label node cons
-- statement:
--   The Tree construction uses the has Label node cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L259-L272
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L259-L272

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}
open DeciSigma1.Semantics.Tree

theorem DeciSigma1.Semantics.Tree.hasLabel_node_cons (a : Fin n → Tree n) (i : Fin n) (w : List (Fin n))
    (s : Sym) (hs : s ≠ Sym.f) :
    HasLabel (Tree.node a) (i :: w) s ↔ HasLabel (a i) w s := by sorry
