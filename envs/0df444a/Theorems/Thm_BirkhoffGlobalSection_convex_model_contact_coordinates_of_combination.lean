-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_coordinates_of_combination
-- name    : BirkhoffGlobalSection.convex_model_contact_coordinates_of_combination
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:42:11.270569+00:00
-- url     : https://prove2.me/theorems/a683497b-b1b9-44db-bf0b-2491985d1ecc
-- title:
--   Convex model contact coordinates of combination
-- statement:
--   The contact coordinates of a linear combination of the two normalized convex model frame vectors are precisely its two coefficients.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 4 of the Proved theorem BirkhoffGlobalSection.contact_frame_angle_disk_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_angle_disk_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_coordinates_of_combination :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere) (a b : ℝ),
    convexModelContactCoordinates M u (a • convexModelSymplecticContactFrame M u 0 +
      b • convexModelSymplecticContactFrame M u 1) = ![a, b] := by sorry
