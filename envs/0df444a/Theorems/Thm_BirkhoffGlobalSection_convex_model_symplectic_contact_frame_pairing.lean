-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_symplectic_contact_frame_pairing
-- name    : BirkhoffGlobalSection.convex_model_symplectic_contact_frame_pairing
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:41:04.878987+00:00
-- url     : https://prove2.me/theorems/c0db829f-27f5-45d7-9532-658e4bbcec51
-- title:
--   Convex model symplectic contact frame pairing
-- statement:
--   The normalized convex model symplectic contact-frame pair has unit weighted exterior pairing with the stated orientation convention.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 13 of the Proved theorem BirkhoffGlobalSection.contact_frame_basis_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_basis_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_symplectic_contact_frame_pairing :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
    let A := convexModelSymplecticContactFrame M u 0
    let B := convexModelSymplecticContactFrame M u 1
    fderiv ℝ (fun x => f x * phaseRadialContact x B) u A -
      fderiv ℝ (fun x => f x * phaseRadialContact x A) u B = 1 := by sorry
