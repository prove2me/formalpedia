-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_radial_inverse_maps_tangent
-- name    : BirkhoffGlobalSection.convex_model_radial_inverse_maps_tangent
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:17:36.53223+00:00
-- url     : https://prove2.me/theorems/f5537e97-89a7-41f2-a902-65c5ab6ed229
-- title:
--   Convex model radial inverse maps tangent
-- statement:
--   The derivative of the inverse radial chart sends model energy-tangent boundary vectors to sphere-tangent vectors.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 11 of the Proved theorem BirkhoffGlobalSection.reverse_radial_variation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_reverse_radial_variation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_reverse_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_radial_inverse_maps_tangent :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y w : Phase) (hy : y ∈ frontier M.body)
    (hw : fderiv ℝ M.modelHamiltonian y w = 0),
    let u := radialNormalize y
    let v := fderiv ℝ radialNormalize y w
    u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0 := by sorry
