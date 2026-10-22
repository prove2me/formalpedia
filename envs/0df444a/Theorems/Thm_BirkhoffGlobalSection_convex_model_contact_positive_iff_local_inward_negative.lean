-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_positive_iff_local_inward_negative
-- name    : BirkhoffGlobalSection.convex_model_contact_positive_iff_local_inward_negative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:12:43.138123+00:00
-- url     : https://prove2.me/theorems/6c4ee1fe-000b-48a5-8a9a-956e121f7190
-- title:
--   Convex model contact positive iff local inward negative
-- statement:
--   For a convex regularization model, positivity of the Hamiltonian contact pairing on the boundary is equivalent to local inward radial negativity at every boundary point.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 11 of the Proved theorem BirkhoffGlobalSection.radial_characteristic_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_radial_characteristic_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_radial_characteristic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_positive_iff_local_inward_negative :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c),
    (∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y)) ↔
    (∀ y ∈ frontier M.body, ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, 1 - ε ≤ t → t < 1 → M.modelHamiltonian (t • y) < 0) := by sorry
