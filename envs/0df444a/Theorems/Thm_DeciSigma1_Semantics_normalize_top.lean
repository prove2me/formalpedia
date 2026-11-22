-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_normalize_top
-- name    : DeciSigma1.Semantics.normalize_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:11.807559+00:00
-- url     : https://prove2.me/theorems/f3573b74-6a1d-4312-93a9-12895cd93259
-- title:
--   Semantics: normalize top
-- statement:
--   The Semantics construction uses the normalize top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L119-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L119-L122

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Semantics.normalize_top (c : Fin n → Bool) (p : Bool) :
    Tree.normalize c p Tree.top = if p then Tree.bot else Tree.top := by sorry
