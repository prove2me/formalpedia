-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_LowerAt_decompose_lower
-- name    : DeciSigma1.Constraints.LowerAt.decompose_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:27:33.8678+00:00
-- url     : https://prove2.me/theorems/a55043bd-2925-40c5-a73d-b705be09d1c1
-- title:
--   Lower At: decompose lower
-- statement:
--   Cancel an upper path from a lower path.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L426-L436
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L426-L436

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

theorem DeciSigma1.Constraints.LowerAt.decompose_lower {π π' : List (Fin n)} {v u w : V}
    (hl : LowerAt Γ (π ++ π') v u) (hu : UpperAt Γ π u w) :
    LowerAt Γ π' v w := by sorry
