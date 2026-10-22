-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_variation_narrow_winding_interval
-- name    : BirkhoffGlobalSection.convex_model_contact_variation_narrow_winding_interval
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:51:52.744975+00:00
-- url     : https://prove2.me/theorems/84b1340a-a1a7-4a27-b7a7-fb5f4a7057ea
-- title:
--   Convex model contact variation narrow winding interval
-- statement:
--   For supplied identity-initialized convex model contact variational data, the directional winding interval has width strictly below one half and satisfies the displayed one-turn threshold equivalence. This does not identify a Conley–Zehnder index.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 7 of the Proved theorem BirkhoffGlobalSection.contact_winding_width_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_winding_width_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_winding_width_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_variation_narrow_winding_interval :
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
      b - a < 1 / 2 ∧
      ((3 : ℤ) ≤ Int.ceil a + Int.ceil b - 1 ↔
        ∀ s ∈ Icc 0 (2 * Real.pi), 2 * Real.pi < θ (T, s) - s) := by sorry
