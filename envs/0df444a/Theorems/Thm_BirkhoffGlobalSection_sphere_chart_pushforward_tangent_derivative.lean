-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_sphere_chart_pushforward_tangent_derivative
-- name    : BirkhoffGlobalSection.sphere_chart_pushforward_tangent_derivative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:15:49.014985+00:00
-- url     : https://prove2.me/theorems/559bf436-3486-4718-ad6e-37282c3ccea2
-- title:
--   Sphere chart pushforward tangent derivative
-- statement:
--   A smooth chart relating vector fields on the sphere satisfies the differentiated pushforward identity in every sphere-tangent direction.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 4 of the Proved theorem BirkhoffGlobalSection.radial_variation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_radial_variation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.sphere_chart_pushforward_tangent_derivative :
∀ (f R X : Phase → Phase) (u w : Phase) (hu : u ∈ unitThreeSphere)
    (hw : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0)
    (hf : ContDiffAt ℝ ∞ f u)
    (hR : DifferentiableAt ℝ R u) (hX : DifferentiableAt ℝ X (f u))
    (hpush : ∀ z ∈ unitThreeSphere, fderiv ℝ f z (R z) = X (f z)),
    fderiv ℝ (fderiv ℝ f) u (R u) w + fderiv ℝ f u (fderiv ℝ R u w) =
      fderiv ℝ X (f u) (fderiv ℝ f u w) := by sorry
