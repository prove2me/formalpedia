-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_coordinates_zero_iff
-- name    : BirkhoffGlobalSection.convex_model_contact_coordinates_zero_iff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:43:19.149855+00:00
-- url     : https://prove2.me/theorems/0c613026-4e5c-409b-a1a1-f662e5d91c19
-- title:
--   Convex model contact coordinates zero iff
-- statement:
--   For a sphere-contact vector, vanishing of both convex model contact coordinates is equivalent to vanishing of the vector.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 5 of the Proved theorem BirkhoffGlobalSection.contact_frame_angle_disk_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_angle_disk_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_coordinates_zero_iff :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v : Phase) (hu : u ∈ unitThreeSphere)
    (hv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0)
    (hα : phaseRadialContact u v = 0),
    convexModelContactCoordinates M u v = 0 ↔ v = 0 := by sorry
