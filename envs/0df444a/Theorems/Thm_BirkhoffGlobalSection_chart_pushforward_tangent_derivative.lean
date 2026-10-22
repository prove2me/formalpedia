-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_chart_pushforward_tangent_derivative
-- name    : BirkhoffGlobalSection.chart_pushforward_tangent_derivative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:15:43.44254+00:00
-- url     : https://prove2.me/theorems/a8d6c91e-f994-4bbf-a0fe-d15e23a7e074
-- title:
--   Chart pushforward tangent derivative
-- statement:
--   If two differentiable vector fields are related by a smooth chart along a supplied tangent curve, differentiating that relation gives the stated tangent pushforward identity.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 2 of the Proved theorem BirkhoffGlobalSection.radial_variation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_radial_variation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.chart_pushforward_tangent_derivative :
∀ (f R X : Phase → Phase) (u w : Phase) (γ : ℝ → Phase)
    (hf : ContDiffAt ℝ ∞ f u)
    (hR : DifferentiableAt ℝ R u) (hX : DifferentiableAt ℝ X (f u))
    (hγ0 : γ 0 = u) (hγ : HasDerivAt γ w 0)
    (heq : (fun s => fderiv ℝ f (γ s) (R (γ s))) =ᶠ[𝓝 0]
      (fun s => X (f (γ s)))),
    fderiv ℝ (fderiv ℝ f) u (R u) w + fderiv ℝ f u (fderiv ℝ R u w) =
      fderiv ℝ X (f u) (fderiv ℝ f u w) := by sorry
