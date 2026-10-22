-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_variation_path_reconstruction
-- name    : BirkhoffGlobalSection.convex_model_contact_variation_path_reconstruction
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:47:16.832635+00:00
-- url     : https://prove2.me/theorems/c698c143-6ca9-4a89-ad6a-184f53239ead
-- title:
--   Convex model contact variation path reconstruction
-- statement:
--   Under the stated supplied Reeb trajectory and variational hypotheses, the evolved contact vector is reconstructed from the contact-coordinate action and the current normalized frame.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 11 of the Proved theorem BirkhoffGlobalSection.contact_variation_preservation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_variation_preservation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_variation_path_reconstruction :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (p : Plane),
    let e := p 0 • convexModelSymplecticContactFrame M (q 0) 0 +
      p 1 • convexModelSymplecticContactFrame M (q 0) 1
    ∀ t, (q t 0 * Z t e 0 + q t 1 * Z t e 1 +
        q t 2 * Z t e 2 + q t 3 * Z t e 3 = 0) ∧
      phaseRadialContact (q t) (Z t e) = 0 ∧
      Z t e = convexModelContactVariationPath M q Z t p 0 •
          convexModelSymplecticContactFrame M (q t) 0 +
        convexModelContactVariationPath M q Z t p 1 •
          convexModelSymplecticContactFrame M (q t) 1 := by sorry
