-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_LowerAt_factor
-- name    : DeciSigma1.Constraints.LowerAt.factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:21:28.807794+00:00
-- url     : https://prove2.me/theorems/9e15cef4-84c0-4760-a583-9e6565d54995
-- title:
--   Lower At: factor
-- statement:
--   The Lower At construction uses the factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L454-L463
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L454-L463

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

theorem DeciSigma1.Constraints.LowerAt.factor {π π' : List (Fin n)} {x z : V}
    (h : LowerAt Γ (π ++ π') x z) :
    ∃ w, LowerAt Γ π w z ∧ LowerAt Γ π' x w := by sorry
