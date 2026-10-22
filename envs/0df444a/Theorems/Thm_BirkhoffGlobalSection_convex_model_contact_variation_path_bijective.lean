-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_variation_path_bijective
-- name    : BirkhoffGlobalSection.convex_model_contact_variation_path_bijective
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:48:50.403981+00:00
-- url     : https://prove2.me/theorems/53dc0bf9-5bc6-40a3-9d7b-075b12f0d775
-- title:
--   Convex model contact variation path bijective
-- statement:
--   At every time, the supplied identity-initialized convex model contact variational action is bijective under the stated Reeb and variational hypotheses.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 12 of the Proved theorem BirkhoffGlobalSection.variational_symplecticity_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_variational_symplecticity_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_variation_path_bijective :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (t : ℝ),
    Function.Bijective (convexModelContactVariationPath M q Z t) := by sorry
