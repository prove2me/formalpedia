-- Prove2me | Theorems.Thm_BalanceSpecification_disjoint_cylinder
-- name    : BalanceSpecification.disjoint_cylinder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:32.738864+00:00
-- url     : https://prove2.me/theorems/0cc5df3b-fd21-4089-9906-6f31c32c3092
-- title:
--   Balance Specification: disjoint cylinder
-- statement:
--   Distinct words of the same length determine disjoint cylinders.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L74-L82
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L74-L82

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

theorem BalanceSpecification.disjoint_cylinder (X : ShiftSpace A) {v w : Word A}
    (hlen : v.length = w.length) (hne : v ≠ w) (k : ℤ) :
    Disjoint (cylinder X v k) (cylinder X w k) := by sorry
