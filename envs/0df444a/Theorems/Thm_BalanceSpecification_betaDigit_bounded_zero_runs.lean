-- Prove2me | Theorems.Thm_BalanceSpecification_betaDigit_bounded_zero_runs
-- name    : BalanceSpecification.betaDigit_bounded_zero_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:58:52.813824+00:00
-- url     : https://prove2.me/theorems/6fd0cc26-e393-4ec7-b279-7a8f352ce5c6
-- title:
--   Balance Specification: beta Digit bounded zero runs
-- statement:
--   Positive bounded residuals exclude zero runs of unbounded length.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyRealization.lean#L70-L89
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyRealization.lean#L70-L89

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

theorem BalanceSpecification.betaDigit_bounded_zero_runs {β a x R : ℝ} (hβ : 1 < β) (ha : 0 < a)
    (hax : a ≤ x) (hxR : x ≤ R) (haR : 1 + a ≤ R) (hR : (β - 1) * R ≤ 1) :
    ∃ N : ℕ, ∀ m : ℕ, ∃ i : ℕ, m ≤ i ∧ i ≤ m + N ∧ betaDigit β a x i = 1 := by sorry
