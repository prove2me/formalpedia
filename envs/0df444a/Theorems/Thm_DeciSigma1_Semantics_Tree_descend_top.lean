-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_descend_top
-- name    : DeciSigma1.Semantics.Tree.descend_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:38.40567+00:00
-- url     : https://prove2.me/theorems/9d1490e5-aa09-4400-a4b4-8bf7a32f173e
-- title:
--   Tree: descend top
-- statement:
--   The Tree construction uses the descend top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L200-L201
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L200-L201

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

theorem DeciSigma1.Semantics.Tree.descend_top (i : Fin n) : descend Tree.top i = Tree.top := by sorry
