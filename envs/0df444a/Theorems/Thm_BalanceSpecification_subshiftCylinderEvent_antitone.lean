-- Prove2me | Theorems.Thm_BalanceSpecification_subshiftCylinderEvent_antitone
-- name    : BalanceSpecification.subshiftCylinderEvent_antitone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:14:25.611346+00:00
-- url     : https://prove2.me/theorems/daa50ec4-5fd8-4e1c-aa75-95e76d90ec85
-- title:
--   Balance Specification: subshift Cylinder Event antitone
-- statement:
--   The Balance Specification construction uses the subshift Cylinder Event antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsEntropyMinimal.lean#L91-L98
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsEntropyMinimal.lean#L91-L98

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

theorem BalanceSpecification.subshiftCylinderEvent_antitone (X Y : ShiftSpace A) :
    Antitone (subshiftCylinderEvent X Y) := by sorry
