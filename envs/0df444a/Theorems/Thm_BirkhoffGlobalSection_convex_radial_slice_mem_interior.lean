-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_radial_slice_mem_interior
-- name    : BirkhoffGlobalSection.convex_radial_slice_mem_interior
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:12:46.183988+00:00
-- url     : https://prove2.me/theorems/dd24f845-500c-4ce9-8711-f007d2b93e32
-- title:
--   Convex radial slice mem interior
-- statement:
--   If zero lies in the interior of a convex set in a real normed space, every scalar multiple t y with y in its closure and 0 ≤ t < 1 lies in its interior.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 12 of the Proved theorem BirkhoffGlobalSection.radial_characteristic_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_radial_characteristic_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_radial_characteristic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

universe u_convex_radial_slice_mem_interior

theorem BirkhoffGlobalSection.convex_radial_slice_mem_interior :
∀ {E : Type u_convex_radial_slice_mem_interior}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E) (hK : Convex ℝ K)
    (h0 : (0 : E) ∈ interior K) (y : E) (hy : y ∈ closure K)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1),
    t • y ∈ interior K := by sorry
