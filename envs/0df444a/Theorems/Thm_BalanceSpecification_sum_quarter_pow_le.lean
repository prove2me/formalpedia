-- Prove2me | Theorems.Thm_BalanceSpecification_sum_quarter_pow_le
-- name    : BalanceSpecification.sum_quarter_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:56:50.419319+00:00
-- url     : https://prove2.me/theorems/3f54fec2-efbe-4f63-b2c1-c9d6b94ca13a
-- title:
--   Balance Specification: sum quarter pow le
-- statement:
--   A finite shifted quarter-geometric sum is at most one third.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEstimates.lean#L26-L35
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEstimates.lean#L26-L35

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

theorem BalanceSpecification.sum_quarter_pow_le (N : ℕ) :
    (∑ n ∈ Finset.range N, ((1 : ℝ) / 4) ^ (n + 1)) ≤ 1 / 3 := by sorry
