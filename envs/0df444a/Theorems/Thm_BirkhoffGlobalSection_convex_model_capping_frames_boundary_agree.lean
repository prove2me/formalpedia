-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_capping_frames_boundary_agree
-- name    : BirkhoffGlobalSection.convex_model_capping_frames_boundary_agree
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:43:45.719126+00:00
-- url     : https://prove2.me/theorems/e4f1f317-d88f-4006-bdf7-b6dafe5c5e7e
-- title:
--   Convex model capping frames boundary agree
-- statement:
--   Two supplied capping disks with identical boundary maps induce identical global-frame restrictions on that boundary.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 11 of the Proved theorem BirkhoffGlobalSection.contact_frame_angle_disk_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_angle_disk_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_capping_frames_boundary_agree :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (d₁ d₂ : ClosedDiskPoint → Phase)
    (hbd : ∀ z : {z : ClosedDiskPoint // z ∈ closedDiskBoundary}, d₁ z.val = d₂ z.val),
    ∀ z : {z : ClosedDiskPoint // z ∈ closedDiskBoundary}, ∀ i : Fin 2,
      convexModelSymplecticContactFrame M (d₁ z.val) i =
        convexModelSymplecticContactFrame M (d₂ z.val) i := by sorry
