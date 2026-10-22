-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_sphere_reeb_normalization_derivative
-- name    : BirkhoffGlobalSection.sphere_reeb_normalization_derivative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:45:14.617988+00:00
-- url     : https://prove2.me/theorems/2b3d024f-a128-43cd-b97c-598a80097218
-- title:
--   Sphere reeb normalization derivative
-- statement:
--   Differentiating the weighted sphere Reeb normalization identity in a sphere-tangent direction gives the displayed derivative relation when the weight is smooth and positive on the sphere.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 3 of the Proved theorem BirkhoffGlobalSection.contact_variation_preservation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_variation_preservation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.sphere_reeb_normalization_derivative :
∀ (f : Phase → ℝ) (u w : Phase)
    (hu : u ∈ unitThreeSphere)
    (hw : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0)
    (hf : ∀ x ∈ unitThreeSphere, ContDiffAt ℝ ∞ f x ∧ 0 < f x),
    let R := sphereReebExtension f
    fderiv ℝ f u w * phaseRadialContact u (R u) +
      f u * (phaseRadialContact w (R u) +
        phaseRadialContact u (fderiv ℝ R u w)) = 0 := by sorry
