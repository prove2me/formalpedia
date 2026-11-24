-- Prove2me | Theorems.Thm_BalanceSpecification_borel_eq_generateFrom_centeredCylinderFamily
-- name    : BalanceSpecification.borel_eq_generateFrom_centeredCylinderFamily
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:20:06.829862+00:00
-- url     : https://prove2.me/theorems/9ef0967e-dbaf-4485-af43-d4480c649977
-- title:
--   Balance Specification: borel eq generate From centered Cylinder Family
-- statement:
--   The literal Borel sigma algebra has the same centered-cylinder generators.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CylinderAlgebra.lean#L176-L178
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CylinderAlgebra.lean#L176-L178

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
variable [Fintype A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]

theorem BalanceSpecification.borel_eq_generateFrom_centeredCylinderFamily (X : ShiftSpace A) :
    borel X.carrier = MeasurableSpace.generateFrom (centeredCylinderFamily X) := by sorry
