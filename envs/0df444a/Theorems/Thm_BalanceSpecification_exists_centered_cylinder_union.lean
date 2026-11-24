-- Prove2me | Theorems.Thm_BalanceSpecification_exists_centered_cylinder_union
-- name    : BalanceSpecification.exists_centered_cylinder_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:45:37.89835+00:00
-- url     : https://prove2.me/theorems/0dc0ef38-e7cb-40f4-be47-1b83c652c522
-- title:
--   Balance Specification: exists centered cylinder union
-- statement:
--   Every finite-block event is a finite union of equal-length centered cylinders.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CylinderAlgebra.lean#L71-L100
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CylinderAlgebra.lean#L71-L100

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

theorem BalanceSpecification.exists_centered_cylinder_union [Fintype A] {X : ShiftSpace A}
    {E : Set X.carrier} (hE : E ∈ finiteCylinderAlgebra X) :
    ∃ n : ℕ, ∃ S : Finset (Word A),
      (∀ w ∈ S, w ∈ language X ∧ w.length = 2 * n + 1) ∧
      E = ⋃ w ∈ S, cylinder X w (-(n : ℤ)) := by sorry
