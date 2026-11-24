-- Prove2me | Theorems.Thm_BalanceSpecification_GibbsBounds_cylinder_real_pos
-- name    : BalanceSpecification.GibbsBounds.cylinder_real_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:30.104569+00:00
-- url     : https://prove2.me/theorems/119b7d85-33a7-4fdc-a062-aca649bb7c69
-- title:
--   Gibbs Bounds: cylinder real pos
-- statement:
--   Admissible cylinders have strictly positive probability under a Gibbs measure.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L147-L152
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L147-L152

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

theorem BalanceSpecification.GibbsBounds.cylinder_real_pos {X : ShiftSpace A} {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} {K : ℝ} (hB : GibbsBounds hX μ K)
    {w : Word A} (hw : w ∈ language X) :
    0 < (μ : Measure X.carrier).real (cylinder X w 0) := by sorry
