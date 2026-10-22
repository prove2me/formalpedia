-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_variation_path_area_preserved
-- name    : BirkhoffGlobalSection.convex_model_contact_variation_path_area_preserved
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:49:11.486984+00:00
-- url     : https://prove2.me/theorems/2fe77155-27b7-46c6-a700-c27f0905cf21
-- title:
--   Convex model contact variation path area preserved
-- statement:
--   The supplied identity-initialized convex model variational action preserves standard signed plane area under the stated sphere Reeb differential hypotheses.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 9 of the Proved theorem BirkhoffGlobalSection.variational_symplecticity_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_variational_symplecticity_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_variation_path_area_preserved :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (t : ℝ) (p r : Plane),
    convexModelContactVariationPath M q Z t p 0 * convexModelContactVariationPath M q Z t r 1 -
      convexModelContactVariationPath M q Z t p 1 * convexModelContactVariationPath M q Z t r 0 =
      p 0 * r 1 - p 1 * r 0 := by sorry
