-- Prove2me | Theorems.Thm_BalanceSpecification_centeredCylinderFamily_subset_finiteCylinderAlgebra
-- name    : BalanceSpecification.centeredCylinderFamily_subset_finiteCylinderAlgebra
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:55:33.465322+00:00
-- url     : https://prove2.me/theorems/cd526f59-3792-4748-b6d4-a1bb8378dcc6
-- title:
--   Balance Specification: centered Cylinder Family subset finite Cylinder Algebra
-- statement:
--   The Balance Specification construction uses the centered Cylinder Family subset finite Cylinder Algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CylinderAlgebra.lean#L102-L108
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CylinderAlgebra.lean#L102-L108

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.SetAlgebra
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set MeasurableSpace
open scoped symmDiff ENNReal
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A]

theorem BalanceSpecification.centeredCylinderFamily_subset_finiteCylinderAlgebra (X : ShiftSpace A) :
    centeredCylinderFamily X ⊆ finiteCylinderAlgebra X := by sorry
