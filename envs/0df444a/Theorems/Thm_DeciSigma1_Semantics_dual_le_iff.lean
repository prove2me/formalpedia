-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_dual_le_iff
-- name    : DeciSigma1.Semantics.dual_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:33.120024+00:00
-- url     : https://prove2.me/theorems/c1a692fd-54e9-4930-a98e-40e89e8be196
-- title:
--   Semantics: dual le iff
-- statement:
--   The Semantics construction uses the dual le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L156-L165
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L156-L165

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Semantics.dual_le_iff (t u : Tree n) : Tree.dual t ≤ Tree.dual u ↔ u ≤ t := by sorry
