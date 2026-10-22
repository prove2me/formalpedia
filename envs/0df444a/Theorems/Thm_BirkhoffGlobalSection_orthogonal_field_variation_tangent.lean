-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_orthogonal_field_variation_tangent
-- name    : BirkhoffGlobalSection.orthogonal_field_variation_tangent
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:16:27.170263+00:00
-- url     : https://prove2.me/theorems/81a38ddd-30a2-4dfe-be8a-e5afaa6965c7
-- title:
--   Orthogonal field variation tangent
-- statement:
--   For a supplied trajectory and variational solution of a locally orthogonal vector field, an initially tangent variation remains tangent under the stated regularity and orthogonality hypotheses.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 9 of the Proved theorem BirkhoffGlobalSection.smooth_sphere_reeb_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_smooth_sphere_reeb_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_smooth_sphere_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.orthogonal_field_variation_tangent :
∀ (R : Phase → Phase) (q v : ℝ → Phase)
    (hq : ∀ t, HasDerivAt q (R (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ R (q t) (v t)) t)
    (hR : ∀ t, DifferentiableAt ℝ R (q t))
    (horth : ∀ t, (fun x => x 0 * R x 0 + x 1 * R x 1 +
      x 2 * R x 2 + x 3 * R x 3) =ᶠ[𝓝 (q t)] (fun _ => (0 : ℝ)))
    (h0 : q 0 0 * v 0 0 + q 0 1 * v 0 1 + q 0 2 * v 0 2 + q 0 3 * v 0 3 = 0),
    ∀ t, q t 0 * v t 0 + q t 1 * v t 1 + q t 2 * v t 2 + q t 3 * v t 3 = 0 := by sorry
