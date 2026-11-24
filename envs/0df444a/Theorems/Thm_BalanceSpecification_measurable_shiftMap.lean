-- Prove2me | Theorems.Thm_BalanceSpecification_measurable_shiftMap
-- name    : BalanceSpecification.measurable_shiftMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:02.315824+00:00
-- url     : https://prove2.me/theorems/213b750f-5c7d-4a38-a775-6fe35f214494
-- title:
--   Balance Specification: measurable shift Map
-- statement:
--   The Balance Specification construction uses the measurable shift Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L89-L90
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L89-L90

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

theorem BalanceSpecification.measurable_shiftMap (X : ShiftSpace A) : Measurable (shiftMap X) := by sorry
