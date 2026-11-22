-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_lowerAt_nil_iff
-- name    : DeciSigma1.Constraints.lowerAt_nil_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:19:09.295423+00:00
-- url     : https://prove2.me/theorems/95b1be1b-845b-462b-a975-739de789d39b
-- title:
--   Constraints: lower At nil iff
-- statement:
--   The Constraints construction uses the lower At nil iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L394-L395
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L394-L395

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
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

theorem DeciSigma1.Constraints.lowerAt_nil_iff {x y : V} : LowerAt Γ [] x y ↔ Derives Γ x y := by sorry
