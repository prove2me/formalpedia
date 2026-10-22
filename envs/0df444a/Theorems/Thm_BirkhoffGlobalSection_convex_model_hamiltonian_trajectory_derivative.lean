-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_hamiltonian_trajectory_derivative
-- name    : BirkhoffGlobalSection.convex_model_hamiltonian_trajectory_derivative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:38:58.889202+00:00
-- url     : https://prove2.me/theorems/088b26ec-b730-4165-ad6e-57aabd755b00
-- title:
--   Convex model hamiltonian trajectory derivative
-- statement:
--   A trajectory of the supplied convex model dynamics has derivative equal to the model Hamiltonian vector field at every real time.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_BirkhoffGlobalSection_convex_model_complete_normalized_flow_of_model_fields.lean:405. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

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

open Set
open scoped Topology ContDiff



set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_hamiltonian_trajectory_derivative {μ c : ℝ}
    (M : BirkhoffGlobalSection.ConvexRegularizationModel μ c)
    {φ : Flow ℝ (BirkhoffGlobalSection.LeftEnergyState μ c)}
    (D : BirkhoffGlobalSection.ConvexModelDynamics M φ)
    (s : BirkhoffGlobalSection.ConvexModelState M) (t : ℝ) :
    HasDerivAt (fun v => (D.flow v s : BirkhoffGlobalSection.Phase))
      (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (D.flow t s)) t := by sorry
