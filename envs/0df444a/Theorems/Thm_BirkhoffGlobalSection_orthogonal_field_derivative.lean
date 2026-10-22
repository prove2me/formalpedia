-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_orthogonal_field_derivative
-- name    : BirkhoffGlobalSection.orthogonal_field_derivative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:16:39.617698+00:00
-- url     : https://prove2.me/theorems/601dccb0-0217-4c48-be4f-6ee5fdc82975
-- title:
--   Orthogonal field derivative
-- statement:
--   If a differentiable vector field is locally orthogonal to the base point, differentiating the orthogonality identity gives the stated pairing identity for its derivative.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 8 of the Proved theorem BirkhoffGlobalSection.smooth_sphere_reeb_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_smooth_sphere_reeb_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_smooth_sphere_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.orthogonal_field_derivative :
∀ (R : Phase → Phase) (u w : Phase)
    (hR : DifferentiableAt ℝ R u)
    (horth : (fun x => x 0 * R x 0 + x 1 * R x 1 +
      x 2 * R x 2 + x 3 * R x 3) =ᶠ[𝓝 u] (fun _ => (0 : ℝ))),
    w 0 * R u 0 + u 0 * (fderiv ℝ R u w) 0 +
    (w 1 * R u 1 + u 1 * (fderiv ℝ R u w) 1) +
    (w 2 * R u 2 + u 2 * (fderiv ℝ R u w) 2) +
    (w 3 * R u 3 + u 3 * (fderiv ℝ R u w) 3) = 0 := by sorry
