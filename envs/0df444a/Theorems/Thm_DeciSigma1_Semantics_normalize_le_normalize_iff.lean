-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_normalize_le_normalize_iff
-- name    : DeciSigma1.Semantics.normalize_le_normalize_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:52.549804+00:00
-- url     : https://prove2.me/theorems/098b0907-5c98-4fb3-8d01-16719e967319
-- title:
--   Semantics: normalize le normalize iff
-- statement:
--   The Semantics construction uses the normalize le normalize iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L391-L393
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L391-L393

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Semantics.Tree
variable {n : ℕ}

theorem DeciSigma1.Semantics.normalize_le_normalize_iff (c : Fin n → Bool) (p : Bool) (t u : Tree n) :
    Tree.normalize c p t ≤ Tree.normalize c p u ↔ if p then Le c u t else Le c t u := by sorry
