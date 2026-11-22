-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_nil
-- name    : DeciSigma1.Semantics.Tree.hasLabel_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:50.79458+00:00
-- url     : https://prove2.me/theorems/21944e4b-dd69-42b4-8204-a792b8c5f42e
-- title:
--   Tree: has Label nil
-- statement:
--   The Tree construction uses the has Label nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L244-L245
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L244-L245

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

theorem DeciSigma1.Semantics.Tree.hasLabel_nil (t : Tree n) (s : Sym) :
    HasLabel t [] s ↔ t.fn [] = some s := by sorry
