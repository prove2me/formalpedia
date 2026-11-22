-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_normalized_signedVar
-- name    : DeciSigma1.Constraints.normalized_signedVar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:37:11.419493+00:00
-- url     : https://prove2.me/theorems/a0d94ed6-bd7c-46e8-bd0c-974100bdf061
-- title:
--   Constraints: normalized signed Var
-- statement:
--   The Constraints construction uses the normalized signed Var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L118-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L118-L120

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

theorem DeciSigma1.Constraints.normalized_signedVar (c : Fin n → Bool) (ρ : V → Semantics.Tree n) (u : V)
    (p : Bool) :
    normalized c ρ (signedVar u p) = Tree.normalize c p (ρ u) := by sorry
