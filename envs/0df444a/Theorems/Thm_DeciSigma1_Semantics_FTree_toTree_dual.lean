-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_dual
-- name    : DeciSigma1.Semantics.FTree.toTree_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:37.694808+00:00
-- url     : https://prove2.me/theorems/e739a120-47bf-4121-8020-2bcd58a138b8
-- title:
--   FTree: to Tree dual
-- statement:
--   The FTree construction uses the to Tree dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L184-L185
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L184-L185

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Semantics.FTree.toTree_dual (t : FTree n) : t.dual.toTree = Tree.dual t.toTree := by sorry
