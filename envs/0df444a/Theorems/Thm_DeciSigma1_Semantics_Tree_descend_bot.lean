-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_descend_bot
-- name    : DeciSigma1.Semantics.Tree.descend_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:36.540834+00:00
-- url     : https://prove2.me/theorems/8b0bfac4-19b9-49d0-9156-6f8c1fa24e3a
-- title:
--   Tree: descend bot
-- statement:
--   The Tree construction uses the descend bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L197-L198
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L197-L198

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

theorem DeciSigma1.Semantics.Tree.descend_bot (i : Fin n) : descend Tree.bot i = Tree.bot := by sorry
