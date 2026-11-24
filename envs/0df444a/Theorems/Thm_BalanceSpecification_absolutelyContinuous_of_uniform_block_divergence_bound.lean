-- Prove2me | Theorems.Thm_BalanceSpecification_absolutelyContinuous_of_uniform_block_divergence_bound
-- name    : BalanceSpecification.absolutelyContinuous_of_uniform_block_divergence_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:10:32.147511+00:00
-- url     : https://prove2.me/theorems/100c8bc7-ad80-4525-bd92-f6fb6aa897ce
-- title:
--   Balance Specification: absolutely Continuous of uniform block divergence bound
-- statement:
--   Uniform finite-cylinder relative entropy bounds imply absolute continuity.
--   This theorem discharges the measure-theoretic passage in the source without
--   assuming a generating-partition convergence theorem for relative entropy.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/AbsoluteContinuity.lean#L138-L228
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/AbsoluteContinuity.lean#L138-L228

module
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_AbsoluteContinuity
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Set Filter
open scoped Topology symmDiff
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.absolutelyContinuous_of_uniform_block_divergence_bound
    {hX : X.carrier.Nonempty} {μ ν : ProbabilityMeasure X.carrier}
    (hG : IsGibbsMeasure hX μ) (hν : IsInvariant ν) {C : ℝ}
    (hD : ∀ n : ℕ, FiniteEntropy.divergence
      (blockDistribution ν (2 * n + 1)) (blockDistribution μ (2 * n + 1)) ≤ C) :
    (ν : Measure X.carrier) ≪ (μ : Measure X.carrier) := by sorry
