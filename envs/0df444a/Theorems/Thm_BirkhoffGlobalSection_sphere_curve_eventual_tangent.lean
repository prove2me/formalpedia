-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_sphere_curve_eventual_tangent
-- name    : BirkhoffGlobalSection.sphere_curve_eventual_tangent
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:17:25.969637+00:00
-- url     : https://prove2.me/theorems/b6043d0c-b1e0-4895-a5df-c19526551f83
-- title:
--   Sphere curve eventual tangent
-- statement:
--   A differentiable curve locally lying on the sphere has sphere-tangent velocity at its base point.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 10 of the Proved theorem BirkhoffGlobalSection.reverse_radial_variation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_reverse_radial_variation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_reverse_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.sphere_curve_eventual_tangent :
∀ (q : ℝ → Phase) (v : Phase) (t : ℝ)
    (hq : ∀ᶠ s in 𝓝 t, q s ∈ unitThreeSphere) (hd : HasDerivAt q v t),
    q t 0 * v 0 + q t 1 * v 1 + q t 2 * v 2 + q t 3 * v 3 = 0 := by sorry
