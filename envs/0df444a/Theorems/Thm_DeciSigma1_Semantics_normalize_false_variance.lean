-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_normalize_false_variance
-- name    : DeciSigma1.Semantics.normalize_false_variance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:13.017357+00:00
-- url     : https://prove2.me/theorems/519af4fb-6d5c-472b-b68c-1eaf451a52bf
-- title:
--   Semantics: normalize false variance
-- statement:
--   The Semantics construction uses the normalize false variance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L132-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L132-L134

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Semantics.normalize_false_variance (t : Tree n) :
    Tree.normalize (fun _ => false) false t = t := by sorry
