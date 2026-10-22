-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_coordinates_reconstruction
-- name    : BirkhoffGlobalSection.convex_model_contact_coordinates_reconstruction
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:41:44.859795+00:00
-- url     : https://prove2.me/theorems/32fe72a3-2b30-469b-b86d-60236f98362a
-- title:
--   Convex model contact coordinates reconstruction
-- statement:
--   A sphere-contact vector is reconstructed from its two convex model contact coordinates and the normalized frame.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 3 of the Proved theorem BirkhoffGlobalSection.contact_frame_angle_disk_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_angle_disk_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_coordinates_reconstruction :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v : Phase) (hu : u ∈ unitThreeSphere)
    (hv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0)
    (hα : phaseRadialContact u v = 0),
    v = (convexModelContactCoordinates M u v 0) • convexModelSymplecticContactFrame M u 0 +
      (convexModelContactCoordinates M u v 1) • convexModelSymplecticContactFrame M u 1 := by sorry
