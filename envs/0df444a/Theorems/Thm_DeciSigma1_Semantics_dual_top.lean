-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_dual_top
-- name    : DeciSigma1.Semantics.dual_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:18.00281+00:00
-- url     : https://prove2.me/theorems/5836807e-373b-49d1-8756-51ada1ed7571
-- title:
--   Semantics: dual top
-- statement:
--   The Semantics construction uses the dual top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L145-L145
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L145-L145

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Semantics.dual_top : Tree.dual (Tree.top : Tree n) = Tree.bot := by sorry
