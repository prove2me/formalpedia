-- Prove2me | Theorems.Thm_BalanceSpecification_GibbsBounds_cylinder_real_exp_bounds
-- name    : BalanceSpecification.GibbsBounds.cylinder_real_exp_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:03.632209+00:00
-- url     : https://prove2.me/theorems/6b21f9f1-562e-4ab2-ab5f-1de3882f70f2
-- title:
--   Gibbs Bounds: cylinder real exp bounds
-- statement:
--   The usual exponential form of the two Gibbs cylinder bounds.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L156-L178
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L156-L178

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
omit [DiscreteTopology A] [BorelSpace A]

theorem BalanceSpecification.GibbsBounds.cylinder_real_exp_bounds {X : ShiftSpace A}
    {hX : X.carrier.Nonempty} {μ : ProbabilityMeasure X.carrier} {K : ℝ}
    (hB : GibbsBounds hX μ K) {w : Word A} (hw : w ∈ language X) :
    Real.exp (-((w.length : ℝ) * entropy X hX)) / K ≤
        (μ : Measure X.carrier).real (cylinder X w 0) ∧
    (μ : Measure X.carrier).real (cylinder X w 0) ≤
      K * Real.exp (-((w.length : ℝ) * entropy X hX)) := by sorry
