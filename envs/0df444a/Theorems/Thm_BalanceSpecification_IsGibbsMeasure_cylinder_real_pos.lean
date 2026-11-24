-- Prove2me | Theorems.Thm_BalanceSpecification_IsGibbsMeasure_cylinder_real_pos
-- name    : BalanceSpecification.IsGibbsMeasure.cylinder_real_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:26.468264+00:00
-- url     : https://prove2.me/theorems/768cf0c4-1a84-4568-8b13-6bca8026233a
-- title:
--   Is Gibbs Measure: cylinder real pos
-- statement:
--   A Gibbs measure assigns positive real probability to every admissible
--   cylinder at every integer coordinate.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L182-L188
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L182-L188

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

theorem BalanceSpecification.IsGibbsMeasure.cylinder_real_pos {X : ShiftSpace A}
    {hX : X.carrier.Nonempty} {μ : ProbabilityMeasure X.carrier}
    (hG : IsGibbsMeasure hX μ) {w : Word A} (hw : w ∈ language X) (k : ℤ) :
    0 < (μ : Measure X.carrier).real (cylinder X w k) := by sorry
