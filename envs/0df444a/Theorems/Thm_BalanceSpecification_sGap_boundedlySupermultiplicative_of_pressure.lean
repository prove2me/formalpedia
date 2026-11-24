-- Prove2me | Theorems.Thm_BalanceSpecification_sGap_boundedlySupermultiplicative_of_pressure
-- name    : BalanceSpecification.sGap_boundedlySupermultiplicative_of_pressure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:16:05.859202+00:00
-- url     : https://prove2.me/theorems/11300ca7-300a-4f81-b7b8-58fac30ef4ec
-- title:
--   Balance Specification: s Gap boundedly Supermultiplicative of pressure
-- statement:
--   A unit-pressure base yields the BSM bound for the actual shift language.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBSM.lean#L199-L212
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBSM.lean#L199-L212

module
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapBSM
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter Set
open scoped Topology

theorem BalanceSpecification.sGap_boundedlySupermultiplicative_of_pressure
    [TopologicalSpace Bool] [DiscreteTopology Bool] {S : Set ℕ} (hS : S.Nonempty)
    {β : ℝ} (hβ : 1 < β)
    (hroot : HasSum (fun s : S => (β⁻¹)^(s.val + 1)) 1) :
    BoundedlySupermultiplicative (language (sGapShift S)) := by sorry
