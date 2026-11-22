-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_UpperAt_chain
-- name    : DeciSigma1.Constraints.UpperAt.chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:27:58.518827+00:00
-- url     : https://prove2.me/theorems/b77adf92-ca78-4829-9de1-93c29201df80
-- title:
--   Upper At: chain
-- statement:
--   An upper path judgment along a nonempty path, as a chain through all prefixes.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L600-L604
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L600-L604

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

theorem DeciSigma1.Constraints.UpperAt.chain {π : List (Fin n)} {z y : V}
    (h : UpperAt Γ π z y) (hπ : π ≠ []) :
    PathChain (UpperAt Γ) π z y := by sorry
