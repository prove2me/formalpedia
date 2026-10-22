-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_variation_path_linear
-- name    : BirkhoffGlobalSection.convex_model_contact_variation_path_linear
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:45:52.33199+00:00
-- url     : https://prove2.me/theorems/c99aeffb-7a56-4706-8291-60cf588f5560
-- title:
--   Convex model contact variation path linear
-- statement:
--   The contact-coordinate action built from a supplied convex model base curve and linear variational matrix is linear in its initial plane vector at every time.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 8 of the Proved theorem BirkhoffGlobalSection.contact_variation_preservation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_variation_preservation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_variation_path_linear :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (t : ℝ) (p r : Plane) (a b : ℝ),
    convexModelContactVariationPath M q Z t (a • p + b • r) =
      a • convexModelContactVariationPath M q Z t p +
        b • convexModelContactVariationPath M q Z t r := by sorry
