-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Sym_leWithPolarity_iff_flip
-- name    : DeciSigma1.Semantics.Sym.leWithPolarity_iff_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:22.845018+00:00
-- url     : https://prove2.me/theorems/237445fe-a683-4b39-93e8-91520eff4b3b
-- title:
--   Sym: le With Polarity iff flip
-- statement:
--   The Sym construction uses the le With Polarity iff flip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L76-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L76-L78

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics DeciSigma1.Semantics.Sym
open DeciSigma1.Semantics.Sym

theorem DeciSigma1.Semantics.Sym.leWithPolarity_iff_flip (p : Bool) (a b : Sym) :
    LeWithPolarity p a b ↔ flip p a ≤ flip p b := by sorry
