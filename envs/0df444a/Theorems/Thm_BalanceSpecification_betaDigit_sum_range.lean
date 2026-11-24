-- Prove2me | Theorems.Thm_BalanceSpecification_betaDigit_sum_range
-- name    : BalanceSpecification.betaDigit_sum_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:33.148804+00:00
-- url     : https://prove2.me/theorems/3d4c62e8-f133-4170-b8e1-b54e77252f17
-- title:
--   Balance Specification: beta Digit sum range
-- statement:
--   The finite expansion identity, before taking its vanishing remainder limit.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyRealization.lean#L92-L100
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyRealization.lean#L92-L100

module
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyRealization
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open BalanceSpecification

theorem BalanceSpecification.betaDigit_sum_range {β a x : ℝ} (hβ : β ≠ 0) (n : ℕ) :
    (∑ i ∈ Finset.range n, betaDigit β a x i / β ^ (i + 1)) =
      x - betaResidual β a x n / β ^ n := by sorry
