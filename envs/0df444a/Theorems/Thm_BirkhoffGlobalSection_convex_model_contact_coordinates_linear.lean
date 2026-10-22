-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_coordinates_linear
-- name    : BirkhoffGlobalSection.convex_model_contact_coordinates_linear
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:41:18.14098+00:00
-- url     : https://prove2.me/theorems/520a6183-7f12-4245-b7b3-3f50e8d71cc6
-- title:
--   Convex model contact coordinates linear
-- statement:
--   For a fixed convex model sphere point, contact coordinates preserve arbitrary real linear combinations of phase vectors.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 1 of the Proved theorem BirkhoffGlobalSection.contact_frame_angle_disk_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_angle_disk_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_coordinates_linear :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v w : Phase) (a b : ℝ),
    convexModelContactCoordinates M u (a • v + b • w) =
      a • convexModelContactCoordinates M u v + b • convexModelContactCoordinates M u w := by sorry
