-- Prove2me | Theorems.Thm_BalanceSpecification_sGap_boundedlySupermultiplicative
-- name    : BalanceSpecification.sGap_boundedlySupermultiplicative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:53:14.074089+00:00
-- url     : https://prove2.me/theorems/3bd5cbf5-63ac-4a70-8205-7130a8292cd5
-- title:
--   Balance Specification: s Gap boundedly Supermultiplicative
-- statement:
--   Every nonempty S-gap shift is BSM, including finite and singleton gap sets.
--   No pressure equation or growth estimate is assumed in this source theorem.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBSM.lean#L216-L231
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBSM.lean#L216-L231

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

theorem BalanceSpecification.sGap_boundedlySupermultiplicative
    [TopologicalSpace Bool] [DiscreteTopology Bool] {S : Set ℕ} (hS : S.Nonempty) :
    BoundedlySupermultiplicative (language (sGapShift S)) := by sorry
