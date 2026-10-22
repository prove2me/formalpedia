-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_gauge_differential_energy_tangent
-- name    : BirkhoffGlobalSection.convex_model_gauge_differential_energy_tangent
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:38:38.084982+00:00
-- url     : https://prove2.me/theorems/88319e08-ca97-40b4-a0fb-879b4e666a4d
-- title:
--   Convex model gauge differential energy tangent
-- statement:
--   At a model boundary point, the gauge differential annihilates every Hamiltonian energy-tangent vector.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 5 of the Proved theorem BirkhoffGlobalSection.contact_frame_basis_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_basis_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_gauge_differential_energy_tangent :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v : Phase) (hu : u ∈ unitThreeSphere),
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    fderiv ℝ M.modelHamiltonian (G u) (fderiv ℝ G u v) = 0 := by sorry
