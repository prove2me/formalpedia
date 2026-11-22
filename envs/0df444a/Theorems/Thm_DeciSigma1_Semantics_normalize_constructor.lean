-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_normalize_constructor
-- name    : DeciSigma1.Semantics.normalize_constructor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:34.906965+00:00
-- url     : https://prove2.me/theorems/2a2a98e8-9c73-403f-b97b-5d1184316640
-- title:
--   Semantics: normalize constructor
-- statement:
--   The Semantics construction uses the normalize constructor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L100-L103
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L100-L103

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Semantics.normalize_constructor (c : Fin n → Bool) (p : Bool) (t : Tree n)
    (π : List (Fin n)) :
    (Tree.normalize c p t).fn π = some Sym.f ↔ t.fn π = some Sym.f := by sorry
