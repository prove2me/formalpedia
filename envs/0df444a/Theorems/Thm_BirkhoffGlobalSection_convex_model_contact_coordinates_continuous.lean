-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_coordinates_continuous
-- name    : BirkhoffGlobalSection.convex_model_contact_coordinates_continuous
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:45:57.744978+00:00
-- url     : https://prove2.me/theorems/865ae6fa-c64e-4845-b021-b35d773bcff2
-- title:
--   Convex model contact coordinates continuous
-- statement:
--   Along continuous sphere-valued base curves and continuous vector curves, convex model contact coordinates vary continuously.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 7 of the Proved theorem BirkhoffGlobalSection.contact_variation_preservation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_variation_preservation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_coordinates_continuous :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q v : ℝ → Phase)
    (hq : Continuous q) (hv : Continuous v) (hs : ∀ t, q t ∈ unitThreeSphere),
    Continuous (fun t => convexModelContactCoordinates M (q t) (v t)) := by sorry
