-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_sphere_reeb_extension_orthogonal
-- name    : BirkhoffGlobalSection.sphere_reeb_extension_orthogonal
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:16:23.080657+00:00
-- url     : https://prove2.me/theorems/9a64c791-666f-484e-b647-14edb4fa3d06
-- title:
--   Sphere reeb extension orthogonal
-- statement:
--   Where the normalized weight is smooth and positive, the radial sphere Reeb extension is orthogonal to the unnormalized phase point.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 7 of the Proved theorem BirkhoffGlobalSection.smooth_sphere_reeb_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_smooth_sphere_reeb_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_smooth_sphere_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.sphere_reeb_extension_orthogonal :
∀ (f : Phase → ℝ) (x : Phase)
    (hx : 0 < zNormSq x + wNormSq x)
    (hf : ContDiffAt ℝ ∞ f (radialNormalize x)) (hp : 0 < f (radialNormalize x)),
    x 0 * sphereReebExtension f x 0 + x 1 * sphereReebExtension f x 1 +
      x 2 * sphereReebExtension f x 2 + x 3 * sphereReebExtension f x 3 = 0 := by sorry
