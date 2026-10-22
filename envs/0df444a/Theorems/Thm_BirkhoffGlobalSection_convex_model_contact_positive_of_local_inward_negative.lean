-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_positive_of_local_inward_negative
-- name    : BirkhoffGlobalSection.convex_model_contact_positive_of_local_inward_negative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:12:38.965198+00:00
-- url     : https://prove2.me/theorems/8a473011-98c2-4c07-9c61-898b793fb6a6
-- title:
--   Convex model contact positive of local inward negative
-- statement:
--   Local inward radial negativity at every convex model boundary point implies positive Hamiltonian contact pairing there.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 9 of the Proved theorem BirkhoffGlobalSection.radial_characteristic_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_radial_characteristic_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_radial_characteristic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_positive_of_local_inward_negative :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    (hneg : ∀ y ∈ frontier M.body, ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, 1 - ε ≤ t → t < 1 → M.modelHamiltonian (t • y) < 0),
    ∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y) := by sorry
