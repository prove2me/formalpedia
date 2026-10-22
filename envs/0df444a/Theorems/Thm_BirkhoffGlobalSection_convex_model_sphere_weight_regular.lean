-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_sphere_weight_regular
-- name    : BirkhoffGlobalSection.convex_model_sphere_weight_regular
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:16:19.545068+00:00
-- url     : https://prove2.me/theorems/50d759c9-e518-4cfc-a968-9e6ac508f999
-- title:
--   Convex model sphere weight regular
-- statement:
--   The squared inverse-gauge sphere weight of a convex model is smooth and positive at every sphere point.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 5 of the Proved theorem BirkhoffGlobalSection.smooth_sphere_reeb_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_smooth_sphere_reeb_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_smooth_sphere_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_sphere_weight_regular :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
    ContDiffAt ℝ ∞ f u ∧ 0 < f u := by sorry
