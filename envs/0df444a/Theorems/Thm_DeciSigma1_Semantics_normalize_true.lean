-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_normalize_true
-- name    : DeciSigma1.Semantics.normalize_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:28.191558+00:00
-- url     : https://prove2.me/theorems/0b33ace9-b3fb-4996-a7ab-665316643a0b
-- title:
--   Semantics: normalize true
-- statement:
--   The Semantics construction uses the normalize true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L149-L154
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L149-L154

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Semantics.normalize_true (c : Fin n → Bool) (t : Tree n) :
    Tree.normalize c true t = Tree.dual (Tree.normalize c false t) := by sorry
