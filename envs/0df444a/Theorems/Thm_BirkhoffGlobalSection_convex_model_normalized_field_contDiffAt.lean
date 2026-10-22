-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_normalized_field_contDiffAt
-- name    : BirkhoffGlobalSection.convex_model_normalized_field_contDiffAt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:15:54.046757+00:00
-- url     : https://prove2.me/theorems/ebbdf565-e889-44fa-bf2d-4de6c62d9ad7
-- title:
--   Convex model normalized field contDiffAt
-- statement:
--   The contact-normalized Hamiltonian vector field of a convex regularization model is smooth at each boundary point.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 7 of the Proved theorem BirkhoffGlobalSection.radial_variation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_radial_variation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_normalized_field_contDiffAt :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y : Phase) (hy : y ∈ frontier M.body),
    ContDiffAt ℝ ∞ (fun z =>
      (phaseRadialContact z (hamiltonianVectorField M.modelHamiltonian z))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian z) y := by sorry
