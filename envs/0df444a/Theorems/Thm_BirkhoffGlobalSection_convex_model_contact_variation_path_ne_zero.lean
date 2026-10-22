-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_variation_path_ne_zero
-- name    : BirkhoffGlobalSection.convex_model_contact_variation_path_ne_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:49:01.463884+00:00
-- url     : https://prove2.me/theorems/16c9d31d-b8a0-4376-a0ad-e01c770b3d4f
-- title:
--   Convex model contact variation path ne zero
-- statement:
--   A nonzero initial plane vector remains nonzero under the supplied convex model contact variational action at every time.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 13 of the Proved theorem BirkhoffGlobalSection.variational_symplecticity_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_variational_symplecticity_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_variation_path_ne_zero :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (t : ℝ) (p : Plane) (hp : p ≠ 0),
    convexModelContactVariationPath M q Z t p ≠ 0 := by sorry
