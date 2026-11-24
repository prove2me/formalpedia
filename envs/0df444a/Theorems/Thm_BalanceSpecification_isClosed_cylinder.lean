-- Prove2me | Theorems.Thm_BalanceSpecification_isClosed_cylinder
-- name    : BalanceSpecification.isClosed_cylinder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:45:23.020969+00:00
-- url     : https://prove2.me/theorems/5be353ee-bed6-424d-bca9-f21784740ab6
-- title:
--   Balance Specification: is Closed cylinder
-- statement:
--   The Balance Specification construction uses the is Closed cylinder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L35-L37
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L35-L37

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

theorem BalanceSpecification.isClosed_cylinder [DiscreteTopology A] (X : ShiftSpace A) (w : Word A) (k : ℤ) :
    IsClosed (cylinder X w k) := by sorry
