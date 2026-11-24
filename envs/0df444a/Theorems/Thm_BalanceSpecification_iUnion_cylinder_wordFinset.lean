-- Prove2me | Theorems.Thm_BalanceSpecification_iUnion_cylinder_wordFinset
-- name    : BalanceSpecification.iUnion_cylinder_wordFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:55:02.428811+00:00
-- url     : https://prove2.me/theorems/6cda4056-e576-4889-8542-8ba8a6ce6d4e
-- title:
--   Balance Specification: i Union cylinder word Finset
-- statement:
--   Admissible length-`n` cylinders partition the shift at every coordinate.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L259-L266
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L259-L266

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Measures
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
variable [Fintype A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]
omit [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]

theorem BalanceSpecification.iUnion_cylinder_wordFinset (X : ShiftSpace A) (n : ℕ) (k : ℤ) :
    (⋃ w ∈ wordFinset (language X) n, cylinder X w k) = Set.univ := by sorry
