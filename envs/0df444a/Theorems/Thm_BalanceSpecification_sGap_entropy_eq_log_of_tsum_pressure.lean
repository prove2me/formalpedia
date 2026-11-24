-- Prove2me | Theorems.Thm_BalanceSpecification_sGap_entropy_eq_log_of_tsum_pressure
-- name    : BalanceSpecification.sGap_entropy_eq_log_of_tsum_pressure
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:06:49.941676+00:00
-- url     : https://prove2.me/theorems/595e58cb-9cee-47cf-9b8c-791858841f53
-- title:
--   Balance Specification: s Gap entropy eq log of tsum pressure
-- statement:
--   The same pressure formula in the ordinary `tsum` form used by beta expansions.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapEntropy.lean#L243-L253
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapEntropy.lean#L243-L253

module
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Definitions.Def_BalanceSpecificaton_GrowthUpperBounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
public import Theorems.Thm_BalanceSpecification_sGapShift_nonempty

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter Set
open scoped Topology

theorem BalanceSpecification.sGap_entropy_eq_log_of_tsum_pressure [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) {β : ℝ} (hβ : 1 < β)
    (hroot : (∑' s : S, (β ^ (s.val + 1))⁻¹) = 1) :
    entropy (sGapShift S) (sGapShift_nonempty hS) = Real.log β := by sorry
