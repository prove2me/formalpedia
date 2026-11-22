-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_normalize_fn
-- name    : DeciSigma1.Semantics.normalize_fn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:00.592034+00:00
-- url     : https://prove2.me/theorems/1755fe64-1c69-4ab4-943c-0d3545cdde4e
-- title:
--   Semantics: normalize fn
-- statement:
--   The Semantics construction uses the normalize fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L97-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L97-L98

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Semantics.normalize_fn (c : Fin n → Bool) (p : Bool) (t : Tree n) (π : List (Fin n)) :
    (Tree.normalize c p t).fn π = (t.fn π).map (Sym.flip (Bool.xor p (polarity c π))) := by sorry

attribute [defeq] DeciSigma1.Semantics.normalize_fn
