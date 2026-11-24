-- Prove2me | Theorems.Thm_BalanceSpecification_sGap_entropy_eq_log_of_pressure
-- name    : BalanceSpecification.sGap_entropy_eq_log_of_pressure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:01:09.898213+00:00
-- url     : https://prove2.me/theorems/2698e89d-7fe5-4c4a-925c-0fded6a5b8bf
-- title:
--   Balance Specification: s Gap entropy eq log of pressure
-- statement:
--   The actual S-gap shift has the entropy prescribed by its unit renewal pressure.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapEntropy.lean#L231-L240
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapEntropy.lean#L231-L240

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

theorem BalanceSpecification.sGap_entropy_eq_log_of_pressure [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) {β : ℝ} (hβ : 1 < β)
    (hroot : HasSum (fun s : S => (β⁻¹)^(s.val + 1)) 1) :
    entropy (sGapShift S) (sGapShift_nonempty hS) = Real.log β := by sorry
