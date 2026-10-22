-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_sphere_contact_frame_positive
-- name    : BirkhoffGlobalSection.convex_model_sphere_contact_frame_positive
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:36:46.049993+00:00
-- url     : https://prove2.me/theorems/9b227253-31f9-48ef-b7fc-bf518f8d4546
-- title:
--   Convex model sphere contact frame positive
-- statement:
--   At every sphere point, the exterior pairing of the convex model contact-frame vectors is positive with the stated orientation convention.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 12 of the Proved theorem BirkhoffGlobalSection.transverse_contact_frame_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_transverse_contact_frame_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_transverse_contact_frame_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_sphere_contact_frame_positive :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
    let A := convexModelSphereContactFrame M u 0
    let B := convexModelSphereContactFrame M u 1
    0 < fderiv ℝ (fun x => f x * phaseRadialContact x B) u A -
      fderiv ℝ (fun x => f x * phaseRadialContact x A) u B := by sorry
