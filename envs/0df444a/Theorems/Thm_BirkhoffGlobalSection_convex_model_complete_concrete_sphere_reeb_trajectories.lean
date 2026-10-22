-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_complete_concrete_sphere_reeb_trajectories
-- name    : BirkhoffGlobalSection.convex_model_complete_concrete_sphere_reeb_trajectories
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:16:38.86798+00:00
-- url     : https://prove2.me/theorems/2d337ecd-10d9-43da-bd66-02ea69082977
-- title:
--   Convex model complete concrete sphere reeb trajectories
-- statement:
--   Given a convex model and supplied complete model dynamics, there is a complete sphere flow with the displayed concrete Reeb trajectory derivative. Completeness of the model dynamics is an input.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 12 of the Proved theorem BirkhoffGlobalSection.smooth_sphere_reeb_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_smooth_sphere_reeb_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_smooth_sphere_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_complete_concrete_sphere_reeb_trajectories :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    {φ : Flow ℝ (LeftEnergyState μ c)} (D : ConvexModelDynamics M φ),
    ∃ θ : Flow ℝ {u : Phase // u ∈ unitThreeSphere},
      ∀ u t, HasDerivAt (fun s => (θ s u : Phase))
        (convexModelSphereReebField M (θ t u)) t := by sorry
