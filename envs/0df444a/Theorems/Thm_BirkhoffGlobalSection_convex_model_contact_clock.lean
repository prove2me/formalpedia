-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_clock
-- name    : BirkhoffGlobalSection.convex_model_contact_clock
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T23:12:27.300553+00:00
-- url     : https://prove2.me/theorems/e63a4b7b-b8fa-4fc4-bcfb-6eb2676173ea
-- title:
--   Convex model contact clock
-- statement:
--   For supplied complete convex model dynamics and positive boundary contact rate, each trajectory admits a complete differentiable integral contact clock starting at zero.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_BirkhoffGlobalSection_convex_model_complete_normalized_flow_of_model_fields.lean:100. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Theorems.Thm_BirkhoffGlobalSection_convex_model_boundary_contact_positive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Hom.Set
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_characteristic_normalization

import Theorems.Thm_BirkhoffGlobalSection_compact_trajectory_positive_clock
open Set
open scoped Topology ContDiff



set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_clock {μ c : ℝ}
    (M : BirkhoffGlobalSection.ConvexRegularizationModel μ c)
    {φ : Flow ℝ (BirkhoffGlobalSection.LeftEnergyState μ c)}
    (D : BirkhoffGlobalSection.ConvexModelDynamics M φ)
    (hcontact : ∀ y ∈ frontier M.body,
      0 < BirkhoffGlobalSection.phaseRadialContact y
        (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian y))
    (s : BirkhoffGlobalSection.ConvexModelState M) :
    ∃ clock : ℝ ≃o ℝ,
      clock 0 = 0 ∧
      (∀ t, HasDerivAt clock
        (BirkhoffGlobalSection.phaseRadialContact (D.flow t s)
          (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (D.flow t s))) t) ∧
      (∀ t, clock t = ∫ v in (0 : ℝ)..t,
        BirkhoffGlobalSection.phaseRadialContact (D.flow v s)
          (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (D.flow v s))) := by sorry
