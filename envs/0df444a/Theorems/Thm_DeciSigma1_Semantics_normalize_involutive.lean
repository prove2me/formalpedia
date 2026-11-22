-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_normalize_involutive
-- name    : DeciSigma1.Semantics.normalize_involutive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:03.205128+00:00
-- url     : https://prove2.me/theorems/29b9b867-4858-4e3a-82cb-67267d4354ea
-- title:
--   Semantics: normalize involutive
-- statement:
--   The Semantics construction uses the normalize involutive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L105-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L105-L108

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Semantics.normalize_involutive (c : Fin n → Bool) (p : Bool) (t : Tree n) :
    Tree.normalize c p (Tree.normalize c p t) = t := by sorry
