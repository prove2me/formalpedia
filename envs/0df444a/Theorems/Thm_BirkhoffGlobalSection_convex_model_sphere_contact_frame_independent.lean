-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_sphere_contact_frame_independent
-- name    : BirkhoffGlobalSection.convex_model_sphere_contact_frame_independent
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:24:02.61799+00:00
-- url     : https://prove2.me/theorems/2be9de58-5f7d-4e61-bd24-2daa4823b43a
-- title:
--   Convex model sphere contact frame independent
-- statement:
--   At every sphere point, the two convex model contact-frame vectors are linearly independent in the stated two-vector sense.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 11 of the Proved theorem BirkhoffGlobalSection.transverse_contact_frame_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_transverse_contact_frame_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_transverse_contact_frame_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_sphere_contact_frame_independent :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere)
    (a b : ℝ) (hz : a • convexModelSphereContactFrame M u 0 +
      b • convexModelSphereContactFrame M u 1 = 0),
    a = 0 ∧ b = 0 := by sorry
