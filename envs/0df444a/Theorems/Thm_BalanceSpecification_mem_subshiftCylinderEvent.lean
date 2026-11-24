-- Prove2me | Theorems.Thm_BalanceSpecification_mem_subshiftCylinderEvent
-- name    : BalanceSpecification.mem_subshiftCylinderEvent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:50:22.84895+00:00
-- url     : https://prove2.me/theorems/245e2165-8e87-4472-9536-1350c03904c3
-- title:
--   Balance Specification: mem subshift Cylinder Event
-- statement:
--   The Balance Specification construction uses the mem subshift Cylinder Event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsEntropyMinimal.lean#L73-L89
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsEntropyMinimal.lean#L73-L89

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Definitions.Def_BalanceSpecificaton_EntropyMinimal
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsEntropyMinimal
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
variable [Fintype A]

theorem BalanceSpecification.mem_subshiftCylinderEvent {X Y : ShiftSpace A} {n : ℕ} {x : X.carrier} :
    x ∈ subshiftCylinderEvent X Y n ↔
      block x.val (-(n : ℤ)) (2 * n + 1) ∈ language Y := by sorry
