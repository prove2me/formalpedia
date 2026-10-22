-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_sphere_contact_frame_coordinates
-- name    : BirkhoffGlobalSection.convex_model_sphere_contact_frame_coordinates
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:18:27.583244+00:00
-- url     : https://prove2.me/theorems/c40e19e9-f174-4600-b720-074e79cc4eff
-- title:
--   Convex model sphere contact frame coordinates
-- statement:
--   For a sphere-contact vector, the convex model radial pushforward has the displayed transverse coordinates and frame pairings.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 10 of the Proved theorem BirkhoffGlobalSection.transverse_contact_frame_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_transverse_contact_frame_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_transverse_contact_frame_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_sphere_contact_frame_coordinates :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    let g := TangentialHessian.grad M.modelHamiltonian (G u)
    let n := zNormSq g + wNormSq g
    transverseFrameCoordinates g (fderiv ℝ G u (convexModelSphereContactFrame M u 0)) = ![n, 0] ∧
    transverseFrameCoordinates g (fderiv ℝ G u (convexModelSphereContactFrame M u 1)) = ![0, n] := by sorry
