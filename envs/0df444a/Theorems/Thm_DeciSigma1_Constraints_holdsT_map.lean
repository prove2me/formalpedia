-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_holdsT_map
-- name    : DeciSigma1.Constraints.holdsT_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:27.701797+00:00
-- url     : https://prove2.me/theorems/ea555055-db56-4ade-b56f-5cd9aa507cc8
-- title:
--   Constraints: holds T map
-- statement:
--   The Constraints construction uses the holds T map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Basic.lean#L62-L64
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Basic.lean#L62-L64

module
public import Mathlib.Data.Fintype.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Constraints.holdsT_map {V W : Type*} (c : Fin n → Bool)
    (f : V → W) (ρ : W → Semantics.Tree n) (l : LitT n V) :
    HoldsT c ρ (l.map f) ↔ HoldsT c (ρ ∘ f) l := by sorry
