-- Prove2me | Theorems.Thm_BalanceSpecification_cylinder_append
-- name    : BalanceSpecification.cylinder_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:42:53.529007+00:00
-- url     : https://prove2.me/theorems/f812d671-b684-44bb-bfdf-13574a3f69e2
-- title:
--   Balance Specification: cylinder append
-- statement:
--   A concatenated cylinder is the intersection of its adjacent component cylinders.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L54-L71
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L54-L71

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

theorem BalanceSpecification.cylinder_append (X : ShiftSpace A) (v w : Word A) (k : ℤ) :
    cylinder X (v ++ w) k = cylinder X v k ∩ cylinder X w (k + v.length) := by sorry
