-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_upperBot_iff_vars
-- name    : DeciSigma1.Constraints.upperBot_iff_vars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:26:14.158269+00:00
-- url     : https://prove2.me/theorems/3fbc56f5-8a4d-4d0d-8575-05307a123575
-- title:
--   Constraints: upper Bot iff vars
-- statement:
--   The Constraints construction uses the upper Bot iff vars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L348-L350
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L348-L350

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}

theorem DeciSigma1.Constraints.upperBot_iff_vars (Γ : List (LitT n V)) (x : V) :
    UpperBot Γ x ↔ ∃ v ∈ botVars Γ, Derives Γ x v := by sorry
