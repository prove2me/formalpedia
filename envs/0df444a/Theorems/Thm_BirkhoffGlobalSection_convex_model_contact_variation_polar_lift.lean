-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_variation_polar_lift
-- name    : BirkhoffGlobalSection.convex_model_contact_variation_polar_lift
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:50:21.388977+00:00
-- url     : https://prove2.me/theorems/bdbf5aa6-2f3f-406f-b1b7-e73eaca6f777
-- title:
--   Convex model contact variation polar lift
-- statement:
--   For supplied identity-initialized convex model Reeb variational data and a nonzero initial coefficient vector, its contact-coordinate trajectory has continuous positive-radius polar data on all real times.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 6 of the Proved theorem BirkhoffGlobalSection.contact_angular_lift_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_angular_lift_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_angular_lift_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_variation_polar_lift :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (p : Plane) (hp : p ≠ 0),
    ∃ ρ θ : ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧ (∀ t, 0 < ρ t) ∧
      ∀ t, convexModelContactVariationPath M q Z t p =
        ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)] := by sorry
