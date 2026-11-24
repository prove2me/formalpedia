-- Prove2me | Theorems.Thm_BalanceSpecification_hasSum_betaDigit
-- name    : BalanceSpecification.hasSum_betaDigit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:04:34.268562+00:00
-- url     : https://prove2.me/theorems/423a2b5a-ce26-4c8e-8221-b76ea5981dff
-- title:
--   Balance Specification: has Sum beta Digit
-- statement:
--   The positive-residual recursion yields a genuine convergent beta expansion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyRealization.lean#L103-L127
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyRealization.lean#L103-L127

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

theorem BalanceSpecification.hasSum_betaDigit {β a x R : ℝ} (hβ : 1 < β) (ha : 0 < a)
    (hax : a ≤ x) (hxR : x ≤ R) (haR : 1 + a ≤ R) (hR : (β - 1) * R ≤ 1) :
    HasSum (fun n : ℕ => betaDigit β a x n / β ^ (n + 1)) x := by sorry
