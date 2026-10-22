-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_normalized_field_inverse_pushforward
-- name    : BirkhoffGlobalSection.convex_model_normalized_field_inverse_pushforward
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:17:13.94418+00:00
-- url     : https://prove2.me/theorems/21c7a021-7f34-4335-9b54-c21785148f1a
-- title:
--   Convex model normalized field inverse pushforward
-- statement:
--   Radial normalization pushes the convex model normalized Hamiltonian field back to its sphere Reeb field.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 7 of the Proved theorem BirkhoffGlobalSection.reverse_radial_variation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_reverse_radial_variation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_reverse_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_normalized_field_inverse_pushforward :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y : Phase) (hy : y ∈ frontier M.body),
    fderiv ℝ radialNormalize y
      ((phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian y) =
      convexModelSphereReebField M (radialNormalize y) := by sorry
