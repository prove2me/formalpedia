-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_UpperAt_factor
-- name    : DeciSigma1.Constraints.UpperAt.factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:21:46.525144+00:00
-- url     : https://prove2.me/theorems/ae087d61-9439-4804-a05d-bbfdcdbc5852
-- title:
--   Upper At: factor
-- statement:
--   The Upper At construction uses the factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L465-L474
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L465-L474

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

theorem DeciSigma1.Constraints.UpperAt.factor {π π' : List (Fin n)} {z y : V}
    (h : UpperAt Γ (π ++ π') z y) :
    ∃ w, UpperAt Γ π z w ∧ UpperAt Γ π' w y := by sorry
