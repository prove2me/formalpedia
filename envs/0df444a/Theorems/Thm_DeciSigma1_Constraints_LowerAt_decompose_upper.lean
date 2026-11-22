-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_LowerAt_decompose_upper
-- name    : DeciSigma1.Constraints.LowerAt.decompose_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:23:43.251822+00:00
-- url     : https://prove2.me/theorems/288f764c-3876-4d51-be50-813a42d5422d
-- title:
--   Lower At: decompose upper
-- statement:
--   Cancel a lower path from an upper path.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L413-L423
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L413-L423

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

theorem DeciSigma1.Constraints.LowerAt.decompose_upper {π π' : List (Fin n)} {w u v : V}
    (hl : LowerAt Γ π w u) (hu : UpperAt Γ (π ++ π') u v) :
    UpperAt Γ π' w v := by sorry
