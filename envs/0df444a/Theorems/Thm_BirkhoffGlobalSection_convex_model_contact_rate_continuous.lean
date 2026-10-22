-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_rate_continuous
-- name    : BirkhoffGlobalSection.convex_model_contact_rate_continuous
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-03T23:17:13.544967+00:00
-- url     : https://prove2.me/theorems/b0510c14-ad54-4242-a02a-5b2eed7d49a7
-- title:
--   Convex model contact rate continuous
-- statement:
--   The convex model Hamiltonian contact rate is continuous on the model state space.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_BirkhoffGlobalSection_convex_model_complete_normalized_flow_of_model_fields.lean:354. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

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

import Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_contact_continuousAt
open Set
open scoped Topology ContDiff



set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_rate_continuous {μ c : ℝ}
    (M : BirkhoffGlobalSection.ConvexRegularizationModel μ c) :
    Continuous (fun s : BirkhoffGlobalSection.ConvexModelState M =>
      BirkhoffGlobalSection.phaseRadialContact s
        (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian s)) := by sorry
