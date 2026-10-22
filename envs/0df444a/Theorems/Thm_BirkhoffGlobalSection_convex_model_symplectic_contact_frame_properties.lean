-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_symplectic_contact_frame_properties
-- name    : BirkhoffGlobalSection.convex_model_symplectic_contact_frame_properties
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:41:12.742247+00:00
-- url     : https://prove2.me/theorems/852ef147-220b-40fe-8d3a-f5ff510fa150
-- title:
--   Convex model symplectic contact frame properties
-- statement:
--   The normalized symplectic contact frame of a convex model satisfies the displayed sphere tangency and contact-kernel identities.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 14 of the Proved theorem BirkhoffGlobalSection.contact_frame_basis_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_basis_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_symplectic_contact_frame_properties :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere) (i : Fin 2),
    let v := convexModelSymplecticContactFrame M u i
    (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0) ∧
      phaseRadialContact u v = 0 := by sorry
