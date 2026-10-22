-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_radial_left_inverse_tangent
-- name    : BirkhoffGlobalSection.convex_model_radial_left_inverse_tangent
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:17:10.973961+00:00
-- url     : https://prove2.me/theorems/4b4fdb51-4c34-4062-aa59-0bbcd0118768
-- title:
--   Convex model radial left inverse tangent
-- statement:
--   On sphere-tangent vectors, the derivative of radial normalization is a left inverse of the convex model gauge-chart derivative.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 6 of the Proved theorem BirkhoffGlobalSection.reverse_radial_variation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_reverse_radial_variation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_reverse_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_radial_left_inverse_tangent :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u w : Phase) (hu : u ∈ unitThreeSphere)
    (hw : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0),
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    fderiv ℝ radialNormalize (G u) (fderiv ℝ G u w) = w := by sorry
