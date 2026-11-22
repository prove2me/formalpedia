-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_sign_signedVar
-- name    : DeciSigma1.Constraints.sign_signedVar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:48.016666+00:00
-- url     : https://prove2.me/theorems/5c63f1c0-6095-405f-b1d7-56ebcbc56d85
-- title:
--   Constraints: sign signed Var
-- statement:
--   The Constraints construction uses the sign signed Var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L51-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L51-L51

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

theorem DeciSigma1.Constraints.sign_signedVar (u : V) (p : Bool) : sign (signedVar u p) = p := by sorry

attribute [defeq] DeciSigma1.Constraints.sign_signedVar
