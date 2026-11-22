-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_mem_derivedPairs
-- name    : DeciSigma1.Constraints.mem_derivedPairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:20:22.731802+00:00
-- url     : https://prove2.me/theorems/2c50fc8b-cb0e-4a7d-820e-fdbc72b2589e
-- title:
--   Constraints: mem derived Pairs
-- statement:
--   The Constraints construction uses the mem derived Pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L306-L322
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L306-L322

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
variable [Fintype V] [DecidableEq V]

theorem DeciSigma1.Constraints.mem_derivedPairs (Γ : List (LitT n V)) (x y : V) :
    (x, y) ∈ derivedPairs Γ ↔ Derives Γ x y := by sorry
