-- Prove2me | Theorems.Thm_BalanceSpecification_log_le_sGap_entropy_of_pressure
-- name    : BalanceSpecification.log_le_sGap_entropy_of_pressure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:06:39.3478+00:00
-- url     : https://prove2.me/theorems/ccc14516-dcbe-45fc-b1ed-e2b87facc316
-- title:
--   Balance Specification: log le s Gap entropy of pressure
-- statement:
--   A unit renewal pressure sum forces the entropy to be at least its logarithmic base.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapEntropy.lean#L158-L196
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapEntropy.lean#L158-L196

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

theorem BalanceSpecification.log_le_sGap_entropy_of_pressure [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) {β : ℝ} (hβ : 1 < β)
    (hroot : HasSum (fun s : S => (β⁻¹)^(s.val + 1)) 1) :
    Real.log β ≤ entropy (sGapShift S) (sGapShift_nonempty hS) := by sorry
