-- Prove2me | Theorems.Thm_BalanceSpecification_GibbsBounds_quasiBernoulli_upper
-- name    : BalanceSpecification.GibbsBounds.quasiBernoulli_upper
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:45:31.950911+00:00
-- url     : https://prove2.me/theorems/9f4a0946-6c95-4771-9b7c-70689b496ef9
-- title:
--   Gibbs Bounds: quasi Bernoulli upper
-- statement:
--   The upper quasi-Bernoulli bound also holds when the concatenation is forbidden.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L245-L255
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L245-L255

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

theorem BalanceSpecification.GibbsBounds.quasiBernoulli_upper {X : ShiftSpace A} {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} {K : ℝ} (hB : GibbsBounds hX μ K)
    (v w : Word A) :
    (μ : Measure X.carrier).real (cylinder X (v ++ w) 0) ≤
      K ^ 3 * (μ : Measure X.carrier).real (cylinder X v 0) *
        (μ : Measure X.carrier).real (cylinder X w 0) := by sorry
