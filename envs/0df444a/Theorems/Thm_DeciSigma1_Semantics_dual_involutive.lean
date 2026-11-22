-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_dual_involutive
-- name    : DeciSigma1.Semantics.dual_involutive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:14.556352+00:00
-- url     : https://prove2.me/theorems/12b7450d-d733-4858-9915-4bff6caa1521
-- title:
--   Semantics: dual involutive
-- statement:
--   The Semantics construction uses the dual involutive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L142-L143
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L142-L143

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Semantics.dual_involutive (t : Tree n) :
    Tree.dual (Tree.dual t) = t := by sorry
