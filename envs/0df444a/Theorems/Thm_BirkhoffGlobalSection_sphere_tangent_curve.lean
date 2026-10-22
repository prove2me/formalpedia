-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_sphere_tangent_curve
-- name    : BirkhoffGlobalSection.sphere_tangent_curve
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:15:39.817627+00:00
-- url     : https://prove2.me/theorems/22064c1f-2e5b-413e-b837-38cb4475e485
-- title:
--   Sphere tangent curve
-- statement:
--   Every vector orthogonal to a point of the unit three-sphere is the velocity at zero of a curve that locally stays on that sphere.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 3 of the Proved theorem BirkhoffGlobalSection.radial_variation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_radial_variation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.sphere_tangent_curve :
∀ (u w : Phase) (hu : u ∈ unitThreeSphere)
    (hw : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0),
    ∃ γ : ℝ → Phase, γ 0 = u ∧ HasDerivAt γ w 0 ∧
      ∀ᶠ s in 𝓝 0, γ s ∈ unitThreeSphere := by sorry
