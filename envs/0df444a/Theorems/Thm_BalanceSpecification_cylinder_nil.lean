-- Prove2me | Theorems.Thm_BalanceSpecification_cylinder_nil
-- name    : BalanceSpecification.cylinder_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:35:26.474911+00:00
-- url     : https://prove2.me/theorems/00763931-6666-411e-bc45-3a84dd5151d8
-- title:
--   Balance Specification: cylinder nil
-- statement:
--   The empty-word cylinder is the whole shift.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L131-L135
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L131-L135

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
omit [Fintype A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]

theorem BalanceSpecification.cylinder_nil (X : ShiftSpace A) (k : ℤ) :
    cylinder X ([] : Word A) k = Set.univ := by sorry
