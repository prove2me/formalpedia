-- Prove2me | Theorems.Thm_BalanceSpecification_measurableSet_cylinder
-- name    : BalanceSpecification.measurableSet_cylinder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:29.708342+00:00
-- url     : https://prove2.me/theorems/e3dadd7e-6262-4b28-8af8-c253e6a31b60
-- title:
--   Balance Specification: measurable Set cylinder
-- statement:
--   The Balance Specification construction uses the measurable Set cylinder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L86-L87
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L86-L87

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

theorem BalanceSpecification.measurableSet_cylinder (X : ShiftSpace A) (w : Word A) (k : ℤ) :
    MeasurableSet (cylinder X w k) := by sorry
