-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_positive_of_inward_negative
-- name    : BirkhoffGlobalSection.convex_model_contact_positive_of_inward_negative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:12:11.388857+00:00
-- url     : https://prove2.me/theorems/72bf94ab-9f5c-4b81-aead-74b396c977e3
-- title:
--   Convex model contact positive of inward negative
-- statement:
--   If a convex model Hamiltonian is negative on every inward radial segment from its boundary, its Hamiltonian contact pairing is positive on that boundary.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 6 of the Proved theorem BirkhoffGlobalSection.radial_characteristic_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_radial_characteristic_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_radial_characteristic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_positive_of_inward_negative :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    (hneg : ∀ y ∈ frontier M.body, ∀ t : ℝ, 0 ≤ t → t < 1 →
      M.modelHamiltonian (t • y) < 0),
    ∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y) := by sorry
