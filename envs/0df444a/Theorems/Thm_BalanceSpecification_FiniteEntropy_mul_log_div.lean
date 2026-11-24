-- Prove2me | Theorems.Thm_BalanceSpecification_FiniteEntropy_mul_log_div
-- name    : BalanceSpecification.FiniteEntropy.mul_log_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:50:13.489948+00:00
-- url     : https://prove2.me/theorems/0db6ef06-449f-43d2-b4c5-34d142a06a0d
-- title:
--   Finite Entropy: mul log div
-- statement:
--   A zero probability contributes zero to the entropy decomposition.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiniteEntropy.lean#L29-L33
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiniteEntropy.lean#L29-L33

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiniteEntropy
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiniteEntropy
variable {ι : Type*} [Fintype ι]

theorem BalanceSpecification.FiniteEntropy.mul_log_div {p q : ℝ} (hq : 0 < q) :
    p * Real.log (p / q) = p * Real.log p - p * Real.log q := by sorry
