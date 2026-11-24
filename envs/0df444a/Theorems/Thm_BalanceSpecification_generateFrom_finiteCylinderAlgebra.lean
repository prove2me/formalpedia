-- Prove2me | Theorems.Thm_BalanceSpecification_generateFrom_finiteCylinderAlgebra
-- name    : BalanceSpecification.generateFrom_finiteCylinderAlgebra
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:56:00.746266+00:00
-- url     : https://prove2.me/theorems/4b471624-e365-4d02-bae0-e916f8d0509f
-- title:
--   Balance Specification: generate From finite Cylinder Algebra
-- statement:
--   Finite-cylinder events generate the entire Borel measurable space.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CylinderAlgebra.lean#L181-L187
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CylinderAlgebra.lean#L181-L187

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

theorem BalanceSpecification.generateFrom_finiteCylinderAlgebra (X : ShiftSpace A) :
    (inferInstance : MeasurableSpace X.carrier) =
      MeasurableSpace.generateFrom (finiteCylinderAlgebra X) := by sorry
