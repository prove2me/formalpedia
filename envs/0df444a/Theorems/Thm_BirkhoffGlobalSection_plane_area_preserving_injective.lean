-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_plane_area_preserving_injective
-- name    : BirkhoffGlobalSection.plane_area_preserving_injective
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:48:43.549134+00:00
-- url     : https://prove2.me/theorems/845e8548-9345-45b4-ab33-ca8934fbf9f3
-- title:
--   Plane area preserving injective
-- statement:
--   Any map of the real coordinate plane preserving the signed area pairing of every two input vectors is injective; linearity is not an assumption.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 10 of the Proved theorem BirkhoffGlobalSection.variational_symplecticity_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_variational_symplecticity_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.plane_area_preserving_injective :
∀ (A : Plane → Plane)
    (hA : ∀ p r, A p 0 * A r 1 - A p 1 * A r 0 = p 0 * r 1 - p 1 * r 0),
    Function.Injective A := by sorry
