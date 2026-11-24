-- Prove2me | Theorems.Thm_BalanceSpecification_block_eq_drop_take
-- name    : BalanceSpecification.block_eq_drop_take
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:07:35.664809+00:00
-- url     : https://prove2.me/theorems/dc5009eb-f2e7-486a-a3e9-e9cbaa9328ab
-- title:
--   Balance Specification: block eq drop take
-- statement:
--   Reading an interior block agrees with taking its finite-word slice.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L241-L248
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L241-L248

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter
open scoped Topology ENNReal Classical BoundedContinuousFunction
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
omit [Fintype A] [TopologicalSpace A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]

theorem BalanceSpecification.block_eq_drop_take (x : Configuration A) {M a k : ℕ} (h : a + k ≤ M) :
    block x (a : ℤ) k = ((block x 0 M).drop a).take k := by sorry
