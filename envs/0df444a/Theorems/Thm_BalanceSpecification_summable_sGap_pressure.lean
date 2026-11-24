-- Prove2me | Theorems.Thm_BalanceSpecification_summable_sGap_pressure
-- name    : BalanceSpecification.summable_sGap_pressure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:16:02.193702+00:00
-- url     : https://prove2.me/theorems/9d280149-db94-43cc-a2b7-2e66afbb3af4
-- title:
--   Balance Specification: summable s Gap pressure
-- statement:
--   The renewal pressure series is summable at every parameter strictly between zero and one.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBSM.lean#L21-L27
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBSM.lean#L21-L27

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

theorem BalanceSpecification.summable_sGap_pressure {S : Set ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun s : S => q^(s.val + 1)) := by sorry
