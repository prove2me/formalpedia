-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_sphere_reeb_extension_regular
-- name    : BirkhoffGlobalSection.sphere_reeb_extension_regular
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:16:07.271977+00:00
-- url     : https://prove2.me/theorems/700a6ab1-35ed-4934-986e-d1003554ddd6
-- title:
--   Sphere reeb extension regular
-- statement:
--   At a sphere point where the weight is smooth and positive, the radial Reeb extension has the displayed smoothness, tangency and Reeb properties.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 3 of the Proved theorem BirkhoffGlobalSection.smooth_sphere_reeb_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_smooth_sphere_reeb_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_smooth_sphere_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.sphere_reeb_extension_regular :
∀ (f : Phase → ℝ) (u : Phase)
    (hu : u ∈ unitThreeSphere) (hf : ContDiffAt ℝ ∞ f u) (hp : 0 < f u),
    ContDiffAt ℝ ∞ (sphereReebExtension f) u ∧
    (u 0 * sphereReebExtension f u 0 + u 1 * sphereReebExtension f u 1 +
      u 2 * sphereReebExtension f u 2 + u 3 * sphereReebExtension f u 3 = 0) ∧
    f u * phaseRadialContact u (sphereReebExtension f u) = 1 ∧
    (∀ w : Phase, u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
      fderiv ℝ (fun x => f x * phaseRadialContact x w) u (sphereReebExtension f u) -
        fderiv ℝ (fun x => f x * phaseRadialContact x (sphereReebExtension f u)) u w = 0) := by sorry
