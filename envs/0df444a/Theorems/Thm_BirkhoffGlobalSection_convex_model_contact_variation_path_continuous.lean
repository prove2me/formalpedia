-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_variation_path_continuous
-- name    : BirkhoffGlobalSection.convex_model_contact_variation_path_continuous
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:45:43.522598+00:00
-- url     : https://prove2.me/theorems/0fda7e92-bc87-47aa-b5f7-b7d9e3709f75
-- title:
--   Convex model contact variation path continuous
-- statement:
--   For supplied continuous sphere-valued base and variational matrix curves, the convex model contact-coordinate action of each fixed initial plane vector is continuous in time.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 10 of the Proved theorem BirkhoffGlobalSection.contact_variation_preservation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_variation_preservation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_variation_path_continuous :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : Continuous q) (hZ : Continuous Z) (p : Plane),
    Continuous (fun t => convexModelContactVariationPath M q Z t p) := by sorry
