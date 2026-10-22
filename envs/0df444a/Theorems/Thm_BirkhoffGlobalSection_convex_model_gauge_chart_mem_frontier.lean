-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_gauge_chart_mem_frontier
-- name    : BirkhoffGlobalSection.convex_model_gauge_chart_mem_frontier
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:16:57.518988+00:00
-- url     : https://prove2.me/theorems/efc81d25-1a1f-423c-89e7-5d3c9b4e6f63
-- title:
--   Convex model gauge chart mem frontier
-- statement:
--   The inverse-gauge radial chart sends every nonzero phase point to the convex model boundary.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 4 of the Proved theorem BirkhoffGlobalSection.reverse_radial_variation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_reverse_radial_variation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_reverse_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_gauge_chart_mem_frontier :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ≠ 0),
    (gauge M.body u)⁻¹ • u ∈ frontier M.body := by sorry
