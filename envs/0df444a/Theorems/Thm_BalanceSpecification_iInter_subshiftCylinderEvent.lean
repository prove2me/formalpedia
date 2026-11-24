-- Prove2me | Theorems.Thm_BalanceSpecification_iInter_subshiftCylinderEvent
-- name    : BalanceSpecification.iInter_subshiftCylinderEvent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:14:16.282505+00:00
-- url     : https://prove2.me/theorems/c64a20eb-fa75-4de2-9671-c5999eb68a26
-- title:
--   Balance Specification: i Inter subshift Cylinder Event
-- statement:
--   The Balance Specification construction uses the i Inter subshift Cylinder Event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsEntropyMinimal.lean#L100-L104
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsEntropyMinimal.lean#L100-L104

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

theorem BalanceSpecification.iInter_subshiftCylinderEvent (X Y : ShiftSpace A) :
    (⋂ n : ℕ, subshiftCylinderEvent X Y n) = {x : X.carrier | x.val ∈ Y.carrier} := by sorry
