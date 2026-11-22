-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_sat_iff_signed
-- name    : DeciSigma1.Constraints.sat_iff_signed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:37:34.958363+00:00
-- url     : https://prove2.me/theorems/3694a5f2-0ab2-44ed-8fa6-c72c9ee2da67
-- title:
--   Constraints: sat iff signed
-- statement:
--   An assignment solves `Γ` with variance `c` exactly when its normalizations solve the signed
--   translation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L144-L146
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L144-L146

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

theorem DeciSigma1.Constraints.sat_iff_signed (c : Fin n → Bool) (ρ : V → Semantics.Tree n) (Γ : List (LitT n V)) :
    SatT c ρ Γ ↔ Covariant.Sat (normalized c ρ) (signed c Γ) := by sorry
