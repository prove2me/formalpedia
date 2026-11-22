-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_sat_signedLit_signedDual_iff
-- name    : DeciSigma1.Constraints.sat_signedLit_signedDual_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:57.851814+00:00
-- url     : https://prove2.me/theorems/ca79d99d-7571-45bc-a3bc-f840ce954edc
-- title:
--   Constraints: sat signed Lit signed Dual iff
-- statement:
--   The Constraints construction uses the sat signed Lit signed Dual iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L99-L103
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L99-L103

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

theorem DeciSigma1.Constraints.sat_signedLit_signedDual_iff (c : Fin n → Bool) (A : (V × Bool) → Semantics.Tree n)
    (l : LitT n V) :
    Covariant.Sat (Signed.dual A) (signedLit c l) ↔ Covariant.Sat A (signedLit c l) := by sorry
