-- Prove2me | Theorems.Thm_BalanceSpecification_cylinder_eq_empty_of_not_mem_language
-- name    : BalanceSpecification.cylinder_eq_empty_of_not_mem_language
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:28.924795+00:00
-- url     : https://prove2.me/theorems/7f71c215-ccae-4de0-a1d5-c571bf5cd34d
-- title:
--   Balance Specification: cylinder eq empty of not mem language
-- statement:
--   The Balance Specification construction uses the cylinder eq empty of not mem language property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L47-L51
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L47-L51

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

theorem BalanceSpecification.cylinder_eq_empty_of_not_mem_language (X : ShiftSpace A) {w : Word A}
    (hw : w ∉ language X) (k : ℤ) : cylinder X w k = ∅ := by sorry
