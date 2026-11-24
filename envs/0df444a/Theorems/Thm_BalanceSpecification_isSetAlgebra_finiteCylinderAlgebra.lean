-- Prove2me | Theorems.Thm_BalanceSpecification_isSetAlgebra_finiteCylinderAlgebra
-- name    : BalanceSpecification.isSetAlgebra_finiteCylinderAlgebra
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:55:16.134031+00:00
-- url     : https://prove2.me/theorems/26643d70-f3d7-4150-87d6-13fb3db2be73
-- title:
--   Balance Specification: is Set Algebra finite Cylinder Algebra
-- statement:
--   The Balance Specification construction uses the is Set Algebra finite Cylinder Algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CylinderAlgebra.lean#L57-L68
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CylinderAlgebra.lean#L57-L68

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

theorem BalanceSpecification.isSetAlgebra_finiteCylinderAlgebra (X : ShiftSpace A) :
    IsSetAlgebra (finiteCylinderAlgebra X) := by sorry
