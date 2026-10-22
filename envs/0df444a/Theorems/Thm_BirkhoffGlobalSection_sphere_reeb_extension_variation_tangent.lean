-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_sphere_reeb_extension_variation_tangent
-- name    : BirkhoffGlobalSection.sphere_reeb_extension_variation_tangent
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:16:31.685986+00:00
-- url     : https://prove2.me/theorems/71e01c7e-dae0-49cf-a715-65838e313d56
-- title:
--   Sphere reeb extension variation tangent
-- statement:
--   For supplied sphere Reeb trajectories and variational solutions, initial sphere tangency is preserved when the sphere weight is smooth and positive.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 10 of the Proved theorem BirkhoffGlobalSection.smooth_sphere_reeb_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_smooth_sphere_reeb_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_smooth_sphere_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.sphere_reeb_extension_variation_tangent :
∀ (f : Phase → ℝ) (q v : ℝ → Phase)
    (hf : ∀ u ∈ unitThreeSphere, ContDiffAt ℝ ∞ f u ∧ 0 < f u)
    (hqS : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (sphereReebExtension f (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ (sphereReebExtension f) (q t) (v t)) t)
    (h0 : q 0 0 * v 0 0 + q 0 1 * v 0 1 + q 0 2 * v 0 2 + q 0 3 * v 0 3 = 0),
    ∀ t, q t 0 * v t 0 + q t 1 * v t 1 + q t 2 * v t 2 + q t 3 * v t 3 = 0 := by sorry
