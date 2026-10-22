-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_positive_of_local_interior_negative
-- name    : BirkhoffGlobalSection.convex_model_contact_positive_of_local_interior_negative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:12:55.909987+00:00
-- url     : https://prove2.me/theorems/21b4f92a-7f24-4269-ab38-8c110d82a5a1
-- title:
--   Convex model contact positive of local interior negative
-- statement:
--   If a convex model Hamiltonian is negative on interior points sufficiently near each boundary point, its Hamiltonian contact pairing is positive on the boundary.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 13 of the Proved theorem BirkhoffGlobalSection.radial_characteristic_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_radial_characteristic_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_radial_characteristic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_positive_of_local_interior_negative :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    (hneg : ∀ y ∈ frontier M.body, ∀ᶠ x in nhds y,
      x ∈ interior M.body → M.modelHamiltonian x < 0),
    ∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y) := by sorry
