-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_variation_winding_interval
-- name    : BirkhoffGlobalSection.convex_model_contact_variation_winding_interval
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:51:15.287641+00:00
-- url     : https://prove2.me/theorems/84789603-d825-4ed6-89aa-7642d682c0c6
-- title:
--   Convex model contact variation winding interval
-- statement:
--   For the supplied convex model contact variational action, all directional normalized angle increments at a fixed time form an attained closed interval with the displayed normalized polar data.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 9 of the Proved theorem BirkhoffGlobalSection.contact_winding_interval_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_winding_interval_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_winding_interval_bundle

open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology

set_option maxHeartbeats 800000
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_variation_winding_interval :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (T : ℝ),
    ∃ (ρ θ : ℝ × ℝ → ℝ) (a b : ℝ), Continuous ρ ∧ Continuous θ ∧
      (∀ x, 0 < ρ x) ∧ (∀ s, θ (0, s) = s) ∧
      (∀ x, convexModelContactVariationPath M q Z x.1 ![Real.cos x.2, Real.sin x.2] =
        ![ρ x * Real.cos (θ x), ρ x * Real.sin (θ x)]) ∧
      a ≤ b ∧
      (fun s => (θ (T, s) - s) / (2 * Real.pi)) '' Icc 0 (2 * Real.pi) = Icc a b ∧
      (∃ s ∈ Icc 0 (2 * Real.pi), (θ (T, s) - s) / (2 * Real.pi) = a) ∧
      (∃ s ∈ Icc 0 (2 * Real.pi), (θ (T, s) - s) / (2 * Real.pi) = b) ∧
      ((∀ s ∈ Icc 0 (2 * Real.pi), 2 * Real.pi < θ (T, s) - s) ↔ 1 < a) := by sorry
