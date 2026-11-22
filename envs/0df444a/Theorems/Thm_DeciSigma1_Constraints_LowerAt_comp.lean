-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_LowerAt_comp
-- name    : DeciSigma1.Constraints.LowerAt.comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:21:23.183839+00:00
-- url     : https://prove2.me/theorems/8d89ee64-79e0-48e5-bb43-8891eb1924b8
-- title:
--   Lower At: comp
-- statement:
--   The Lower At construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L440-L445
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L440-L445

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

theorem DeciSigma1.Constraints.LowerAt.comp {π π' : List (Fin n)} {x w z : V}
    (h' : LowerAt Γ π' x w) (h : LowerAt Γ π w z) :
    LowerAt Γ (π ++ π') x z := by sorry
