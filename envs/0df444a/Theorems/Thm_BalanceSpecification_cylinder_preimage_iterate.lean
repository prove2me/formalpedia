-- Prove2me | Theorems.Thm_BalanceSpecification_cylinder_preimage_iterate
-- name    : BalanceSpecification.cylinder_preimage_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:06:37.942566+00:00
-- url     : https://prove2.me/theorems/bf07bcc7-8cab-45d1-96d7-94d049cd8c27
-- title:
--   Balance Specification: cylinder preimage iterate
-- statement:
--   Pulling back a cylinder by an iterate translates its starting coordinate.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L40-L45
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L40-L45

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

theorem BalanceSpecification.cylinder_preimage_iterate (X : ShiftSpace A) (w : Word A) (k : ℤ) (n : ℕ) :
    (shiftMap X)^[n] ⁻¹' cylinder X w k = cylinder X w ((n : ℤ) + k) := by sorry
