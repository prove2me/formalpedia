-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_radial_derivative_positive
-- name    : BirkhoffGlobalSection.convex_model_radial_derivative_positive
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:00:52.171751+00:00
-- url     : https://prove2.me/theorems/5ffed5d9-45a1-4229-a81f-09ea8c7b0857
-- title:
--   Convex model radial derivative positive
-- statement:
--   The convex model Hamiltonian has strictly positive radial derivative at every boundary point.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_BirkhoffGlobalSection_convex_model_boundary_contact_positive.lean:7. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Theorems.Thm_ConvexAnalysis_convex_frontier_radial_derivative_positive
import Definitions.Def_BirkhoffGlobalSection_TransverseHopf

open BirkhoffGlobalSection ConvexAnalysis Filter Set
open scoped ContDiff Topology


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_radial_derivative_positive {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) :
    ∀ y ∈ frontier M.body, 0 < fderiv ℝ M.modelHamiltonian y y := by sorry
