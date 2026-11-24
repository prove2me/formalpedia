-- Prove2me | Theorems.Thm_BalanceSpecification_IsInvariant_cylinder_real_eq_zero
-- name    : BalanceSpecification.IsInvariant.cylinder_real_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:36:08.779382+00:00
-- url     : https://prove2.me/theorems/6316c42b-12ac-4839-bbe9-e92df98668c4
-- title:
--   Is Invariant: cylinder real eq zero
-- statement:
--   Invariance identifies the real cylinder probabilities at all integer coordinates.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L111-L127
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L111-L127

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

theorem BalanceSpecification.IsInvariant.cylinder_real_eq_zero {X : ShiftSpace A}
    {μ : ProbabilityMeasure X.carrier} (hμ : IsInvariant μ) (w : Word A) (k : ℤ) :
    (μ : Measure X.carrier).real (cylinder X w k) =
      (μ : Measure X.carrier).real (cylinder X w 0) := by sorry
