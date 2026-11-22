-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_LowerAt_chain
-- name    : DeciSigma1.Constraints.LowerAt.chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:27:50.460807+00:00
-- url     : https://prove2.me/theorems/cabe8248-d1c8-4034-bf29-32ea329a9d0b
-- title:
--   Lower At: chain
-- statement:
--   A lower path judgment along a nonempty path, as a chain through all prefixes.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L593-L597
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L593-L597

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

theorem DeciSigma1.Constraints.LowerAt.chain {π : List (Fin n)} {x z : V}
    (h : LowerAt Γ π x z) (hπ : π ≠ []) :
    PathChain (fun τ u v => LowerAt Γ τ v u) π z x := by sorry
