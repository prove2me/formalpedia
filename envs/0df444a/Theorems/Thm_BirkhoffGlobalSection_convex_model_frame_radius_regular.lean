-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_frame_radius_regular
-- name    : BirkhoffGlobalSection.convex_model_frame_radius_regular
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:41:05.100271+00:00
-- url     : https://prove2.me/theorems/17d5d9f8-c703-492f-b77e-df4c592928d8
-- title:
--   Convex model frame radius regular
-- statement:
--   The convex model frame-radius factor has the displayed smoothness and positivity at sphere points.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 10 of the Proved theorem BirkhoffGlobalSection.contact_frame_basis_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_basis_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_frame_radius_regular :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    ContDiffAt ℝ ∞ (convexModelFrameRadius M) u ∧ 0 < convexModelFrameRadius M u := by sorry
