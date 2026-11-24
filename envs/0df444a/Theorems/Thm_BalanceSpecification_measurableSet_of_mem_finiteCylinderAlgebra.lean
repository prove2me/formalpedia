-- Prove2me | Theorems.Thm_BalanceSpecification_measurableSet_of_mem_finiteCylinderAlgebra
-- name    : BalanceSpecification.measurableSet_of_mem_finiteCylinderAlgebra
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:55:39.048929+00:00
-- url     : https://prove2.me/theorems/7481a146-4aa3-4e62-8d32-3c33a47e4979
-- title:
--   Balance Specification: measurable Set of mem finite Cylinder Algebra
-- statement:
--   The Balance Specification construction uses the measurable Set of mem finite Cylinder Algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CylinderAlgebra.lean#L112-L115
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CylinderAlgebra.lean#L112-L115

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

theorem BalanceSpecification.measurableSet_of_mem_finiteCylinderAlgebra {X : ShiftSpace A} {E : Set X.carrier}
    (hE : E ∈ finiteCylinderAlgebra X) : MeasurableSet E := by sorry
