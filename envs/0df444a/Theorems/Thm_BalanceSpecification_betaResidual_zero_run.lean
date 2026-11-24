-- Prove2me | Theorems.Thm_BalanceSpecification_betaResidual_zero_run
-- name    : BalanceSpecification.betaResidual_zero_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:58:49.115028+00:00
-- url     : https://prove2.me/theorems/4da34b80-fc2a-4925-a40d-b0dcddab000a
-- title:
--   Balance Specification: beta Residual zero run
-- statement:
--   A run of zero digits makes the residual grow by the corresponding beta power.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyRealization.lean#L59-L67
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyRealization.lean#L59-L67

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

theorem BalanceSpecification.betaResidual_zero_run (β a x : ℝ) (m k : ℕ)
    (hzero : ∀ i : ℕ, i < k → betaDigit β a x (m + i) = 0) :
    betaResidual β a x (m + k) = β ^ k * betaResidual β a x m := by sorry
