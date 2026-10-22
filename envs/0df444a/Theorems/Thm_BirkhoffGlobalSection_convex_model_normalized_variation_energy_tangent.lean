-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_normalized_variation_energy_tangent
-- name    : BirkhoffGlobalSection.convex_model_normalized_variation_energy_tangent
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:16:48.511987+00:00
-- url     : https://prove2.me/theorems/ade18d22-cfcc-4e11-b473-a17ca74acf83
-- title:
--   Convex model normalized variation energy tangent
-- statement:
--   For supplied normalized model trajectories and variational solutions on the boundary, an initially energy-tangent variation remains energy tangent.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 3 of the Proved theorem BirkhoffGlobalSection.reverse_radial_variation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_reverse_radial_variation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_reverse_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_normalized_variation_energy_tangent :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (x v : ℝ → Phase)
    (hs : ∀ t, x t ∈ frontier M.body)
    (hx : ∀ t, HasDerivAt x
      ((phaseRadialContact (x t) (hamiltonianVectorField M.modelHamiltonian (x t)))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian (x t)) t)
    (hv : ∀ t, HasDerivAt v
      (fderiv ℝ (fun y =>
        (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
          hamiltonianVectorField M.modelHamiltonian y) (x t) (v t)) t)
    (h0 : fderiv ℝ M.modelHamiltonian (x 0) (v 0) = 0),
    ∀ t, fderiv ℝ M.modelHamiltonian (x t) (v t) = 0 := by sorry
