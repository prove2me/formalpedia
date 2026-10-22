-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_plane_linear_area_preserving_bijective
-- name    : BirkhoffGlobalSection.plane_linear_area_preserving_bijective
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:48:56.139125+00:00
-- url     : https://prove2.me/theorems/b1e30b5c-f494-4ea7-9f22-7dd42b45d792
-- title:
--   Plane linear area preserving bijective
-- statement:
--   A real-linear map of the coordinate plane preserving the signed area pairing is bijective.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 11 of the Proved theorem BirkhoffGlobalSection.variational_symplecticity_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_variational_symplecticity_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.plane_linear_area_preserving_bijective :
∀ (A : Plane → Plane)
    (hlin : ∀ (p r : Plane) (a b : ℝ), A (a • p + b • r) = a • A p + b • A r)
    (harea : ∀ p r, A p 0 * A r 1 - A p 1 * A r 0 = p 0 * r 1 - p 1 * r 0),
    Function.Bijective A := by sorry
