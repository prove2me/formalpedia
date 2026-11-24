-- Prove2me | Theorems.Thm_BalanceSpecification_measurableSet_subshiftCylinderEvent
-- name    : BalanceSpecification.measurableSet_subshiftCylinderEvent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:14:32.582282+00:00
-- url     : https://prove2.me/theorems/ad1cc319-66b4-45d1-a0b1-de92da4c24fc
-- title:
--   Balance Specification: measurable Set subshift Cylinder Event
-- statement:
--   The Balance Specification construction uses the measurable Set subshift Cylinder Event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsEntropyMinimal.lean#L108-L111
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsEntropyMinimal.lean#L108-L111

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
variable [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]

theorem BalanceSpecification.measurableSet_subshiftCylinderEvent (X Y : ShiftSpace A) (n : ℕ) :
    MeasurableSet (subshiftCylinderEvent X Y n) := by sorry
