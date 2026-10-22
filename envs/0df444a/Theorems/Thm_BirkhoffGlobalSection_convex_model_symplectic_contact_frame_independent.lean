-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_symplectic_contact_frame_independent
-- name    : BirkhoffGlobalSection.convex_model_symplectic_contact_frame_independent
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:41:35.63813+00:00
-- url     : https://prove2.me/theorems/2f83398d-be2f-4c91-9fcb-436381307397
-- title:
--   Convex model symplectic contact frame independent
-- statement:
--   The normalized convex model symplectic contact frame is linearly independent at every sphere point.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 16 of the Proved theorem BirkhoffGlobalSection.contact_frame_basis_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_basis_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_symplectic_contact_frame_independent :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere)
    (a b : ℝ) (hz : a • convexModelSymplecticContactFrame M u 0 +
      b • convexModelSymplecticContactFrame M u 1 = 0),
    a = 0 ∧ b = 0 := by sorry
