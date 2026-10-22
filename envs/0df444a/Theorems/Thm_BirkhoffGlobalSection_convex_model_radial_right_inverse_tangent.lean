-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_radial_right_inverse_tangent
-- name    : BirkhoffGlobalSection.convex_model_radial_right_inverse_tangent
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:17:23.78201+00:00
-- url     : https://prove2.me/theorems/09045e1b-6919-4b0b-9c2e-6b8c682a2420
-- title:
--   Convex model radial right inverse tangent
-- statement:
--   On energy-tangent boundary vectors, the convex model gauge-chart derivative is a right inverse of the radial-normalization derivative.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 8 of the Proved theorem BirkhoffGlobalSection.reverse_radial_variation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_reverse_radial_variation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_reverse_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_radial_right_inverse_tangent :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y w : Phase) (hy : y ∈ frontier M.body)
    (hw : fderiv ℝ M.modelHamiltonian y w = 0),
    fderiv ℝ (fun x : Phase => (gauge M.body x)⁻¹ • x) (radialNormalize y)
      (fderiv ℝ radialNormalize y w) = w := by sorry
