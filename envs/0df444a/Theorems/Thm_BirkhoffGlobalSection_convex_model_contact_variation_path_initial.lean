-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_variation_path_initial
-- name    : BirkhoffGlobalSection.convex_model_contact_variation_path_initial
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:45:55.909828+00:00
-- url     : https://prove2.me/theorems/49a8b806-eeb3-4c48-8b12-76749c856d26
-- title:
--   Convex model contact variation path initial
-- statement:
--   With sphere initial base point and identity initial variational matrix, the convex model contact-coordinate action equals the identity at time zero.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 9 of the Proved theorem BirkhoffGlobalSection.contact_variation_preservation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_variation_preservation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_variation_path_initial :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : q 0 ∈ unitThreeSphere)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (p : Plane),
    convexModelContactVariationPath M q Z 0 p = p := by sorry
