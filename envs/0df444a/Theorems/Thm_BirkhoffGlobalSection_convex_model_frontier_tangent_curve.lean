-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_frontier_tangent_curve
-- name    : BirkhoffGlobalSection.convex_model_frontier_tangent_curve
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:17:00.039022+00:00
-- url     : https://prove2.me/theorems/48529a15-095a-4ec8-9c7b-45cb3346f6af
-- title:
--   Convex model frontier tangent curve
-- statement:
--   At a convex model boundary point, every vector in the Hamiltonian differential kernel is the velocity of a curve locally contained in the boundary.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 5 of the Proved theorem BirkhoffGlobalSection.reverse_radial_variation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_reverse_radial_variation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_reverse_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_frontier_tangent_curve :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y w : Phase) (hy : y ∈ frontier M.body)
    (hw : fderiv ℝ M.modelHamiltonian y w = 0),
    ∃ γ : ℝ → Phase, γ 0 = y ∧ HasDerivAt γ w 0 ∧
      ∀ᶠ s in 𝓝 0, γ s ∈ frontier M.body := by sorry
