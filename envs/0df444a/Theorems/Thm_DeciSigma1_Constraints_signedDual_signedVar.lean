-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_signedDual_signedVar
-- name    : DeciSigma1.Constraints.signedDual_signedVar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:55.316523+00:00
-- url     : https://prove2.me/theorems/c0924ffa-18bf-401a-95f4-619694cb25bf
-- title:
--   Constraints: signed Dual signed Var
-- statement:
--   The Constraints construction uses the signed Dual signed Var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L76-L77
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L76-L77

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

theorem DeciSigma1.Constraints.signedDual_signedVar (A : (V × Bool) → Semantics.Tree n) (u : V) (p : Bool) :
    Signed.dual A (signedVar u p) = Tree.dual (A (signedVar u (!p))) := by sorry
