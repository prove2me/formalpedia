-- Prove2me | Theorems.Thm_BalanceSpecification_sum_cylinder_real_eq_one
-- name    : BalanceSpecification.sum_cylinder_real_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:42:53.826665+00:00
-- url     : https://prove2.me/theorems/cf15cf91-d52a-45ff-8ffe-e0ead60f0302
-- title:
--   Balance Specification: sum cylinder real eq one
-- statement:
--   Their real probabilities sum to one, including the length-zero partition.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L269-L279
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L269-L279

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

theorem BalanceSpecification.sum_cylinder_real_eq_one (X : ShiftSpace A) (μ : ProbabilityMeasure X.carrier)
    (n : ℕ) (k : ℤ) :
    (∑ w ∈ wordFinset (language X) n,
      (μ : Measure X.carrier).real (cylinder X w k)) = 1 := by sorry
