-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_normalize_bot
-- name    : DeciSigma1.Semantics.normalize_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:11.272802+00:00
-- url     : https://prove2.me/theorems/94f8d288-cea5-48e7-88eb-c82b769bdddb
-- title:
--   Semantics: normalize bot
-- statement:
--   The Semantics construction uses the normalize bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L114-L117
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L114-L117

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Semantics.normalize_bot (c : Fin n → Bool) (p : Bool) :
    Tree.normalize c p Tree.bot = if p then Tree.top else Tree.bot := by sorry
