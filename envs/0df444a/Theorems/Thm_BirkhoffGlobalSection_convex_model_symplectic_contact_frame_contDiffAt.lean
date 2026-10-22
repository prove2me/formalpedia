-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_symplectic_contact_frame_contDiffAt
-- name    : BirkhoffGlobalSection.convex_model_symplectic_contact_frame_contDiffAt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:41:14.822359+00:00
-- url     : https://prove2.me/theorems/70ca03b0-a462-4bcd-9b01-0d94e1d41252
-- title:
--   Convex model symplectic contact frame contDiffAt
-- statement:
--   Each normalized symplectic contact-frame vector of a convex model is smooth at every sphere point.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 11 of the Proved theorem BirkhoffGlobalSection.contact_frame_basis_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_basis_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_symplectic_contact_frame_contDiffAt :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere) (i : Fin 2),
    ContDiffAt ℝ ∞ (fun z => convexModelSymplecticContactFrame M z i) u := by sorry
