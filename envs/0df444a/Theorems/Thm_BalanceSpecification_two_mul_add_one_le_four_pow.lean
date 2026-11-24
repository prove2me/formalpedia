-- Prove2me | Theorems.Thm_BalanceSpecification_two_mul_add_one_le_four_pow
-- name    : BalanceSpecification.two_mul_add_one_le_four_pow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:56:48.56599+00:00
-- url     : https://prove2.me/theorems/4654f35d-ded4-4acf-9d8a-72b9111f6e1d
-- title:
--   Balance Specification: two mul add one le four pow
-- statement:
--   Elementary exponential domination used by the sparse marker sequence.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEstimates.lean#L20-L23
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEstimates.lean#L20-L23

module
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerEstimates
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification

theorem BalanceSpecification.two_mul_add_one_le_four_pow (n : ℕ) : 2 * n + 1 ≤ 4 ^ n := by sorry
