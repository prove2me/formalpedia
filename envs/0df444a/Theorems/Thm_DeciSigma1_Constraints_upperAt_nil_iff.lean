-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_upperAt_nil_iff
-- name    : DeciSigma1.Constraints.upperAt_nil_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:19:13.220985+00:00
-- url     : https://prove2.me/theorems/48ce2c59-82e6-4a48-afb0-3ff80b8784a8
-- title:
--   Constraints: upper At nil iff
-- statement:
--   The Constraints construction uses the upper At nil iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L397-L398
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L397-L398

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

theorem DeciSigma1.Constraints.upperAt_nil_iff {x y : V} : UpperAt Γ [] x y ↔ Derives Γ x y := by sorry
