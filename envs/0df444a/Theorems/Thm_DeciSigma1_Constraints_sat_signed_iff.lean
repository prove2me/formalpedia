-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_sat_signed_iff
-- name    : DeciSigma1.Constraints.sat_signed_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:57.48554+00:00
-- url     : https://prove2.me/theorems/e2097a1b-ecca-4ce7-adb0-c6e24295a69b
-- title:
--   Constraints: sat signed iff
-- statement:
--   The Constraints construction uses the sat signed iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L89-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L89-L97

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}

theorem DeciSigma1.Constraints.sat_signed_iff (c : Fin n → Bool) (A : (V × Bool) → Semantics.Tree n)
    (Γ : List (LitT n V)) :
    Covariant.Sat A (signed c Γ) ↔ ∀ l ∈ Γ, Covariant.Sat A (signedLit c l) := by sorry
