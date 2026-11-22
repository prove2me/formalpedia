-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_dual_bot
-- name    : DeciSigma1.Semantics.dual_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:23.6835+00:00
-- url     : https://prove2.me/theorems/b3b9598c-7ecc-4609-9c96-61d23ba6b55e
-- title:
--   Semantics: dual bot
-- statement:
--   The Semantics construction uses the dual bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L144-L144
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L144-L144

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Semantics.dual_bot : Tree.dual (Tree.bot : Tree n) = Tree.top := by sorry
