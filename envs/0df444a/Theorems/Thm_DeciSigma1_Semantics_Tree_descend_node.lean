-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_descend_node
-- name    : DeciSigma1.Semantics.Tree.descend_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:42.884803+00:00
-- url     : https://prove2.me/theorems/5cfed9fe-90a9-4249-8035-27086e2f8a31
-- title:
--   Tree: descend node
-- statement:
--   The Tree construction uses the descend node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L203-L207
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L203-L207

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

theorem DeciSigma1.Semantics.Tree.descend_node (a : Fin n → Tree n) (i : Fin n) :
    descend (Tree.node a) i = a i := by sorry
