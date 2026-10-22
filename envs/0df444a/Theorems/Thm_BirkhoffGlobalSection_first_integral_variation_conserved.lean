-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_first_integral_variation_conserved
-- name    : BirkhoffGlobalSection.first_integral_variation_conserved
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:16:59.907976+00:00
-- url     : https://prove2.me/theorems/4ffa7fdf-b2a9-47af-b925-efcd1e6a2d25
-- title:
--   First integral variation conserved
-- statement:
--   For a smooth first integral and supplied trajectory and variational solution of a differentiable vector field, the first integral's differential applied to the variation is conserved under the displayed local first-integral hypotheses.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 2 of the Proved theorem BirkhoffGlobalSection.reverse_radial_variation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_reverse_radial_variation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_reverse_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.first_integral_variation_conserved :
∀ (F : Phase → ℝ) (X : Phase → Phase)
    (x v : ℝ → Phase) (hF : ∀ t, ContDiffAt ℝ ∞ F (x t))
    (hX : ∀ t, DifferentiableAt ℝ X (x t))
    (hx : ∀ t, HasDerivAt x (X (x t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ X (x t) (v t)) t)
    (hzero : ∀ t, (fun y => fderiv ℝ F y (X y)) =ᶠ[𝓝 (x t)] (fun _ => (0 : ℝ))),
    ∀ t, fderiv ℝ F (x t) (v t) = fderiv ℝ F (x 0) (v 0) := by sorry
