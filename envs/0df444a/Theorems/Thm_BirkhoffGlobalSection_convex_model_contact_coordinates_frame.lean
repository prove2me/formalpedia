-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_coordinates_frame
-- name    : BirkhoffGlobalSection.convex_model_contact_coordinates_frame
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:41:31.494968+00:00
-- url     : https://prove2.me/theorems/4ff999ab-f54a-4554-adf2-f2d20ee57ca6
-- title:
--   Convex model contact coordinates frame
-- statement:
--   The two normalized convex model contact-frame vectors have the standard coordinate vectors (1,0) and (0,1).
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 2 of the Proved theorem BirkhoffGlobalSection.contact_frame_angle_disk_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_angle_disk_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_coordinates_frame :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    convexModelContactCoordinates M u (convexModelSymplecticContactFrame M u 0) = ![1, 0] ∧
    convexModelContactCoordinates M u (convexModelSymplecticContactFrame M u 1) = ![0, 1] := by sorry
