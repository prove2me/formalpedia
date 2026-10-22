-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_radial_contact_exterior_pullback
-- name    : BirkhoffGlobalSection.radial_contact_exterior_pullback
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:11:33.599598+00:00
-- url     : https://prove2.me/theorems/6b448b45-5f24-4888-b7bb-4b5b3a3833aa
-- title:
--   Radial contact exterior pullback
-- statement:
--   For a differentiable radial scale a in real four-dimensional phase space, the exterior derivative of the squared-scale radial contact form equals the negative symplectic pairing of the two radially pushed tangent vectors.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 1 of the Proved theorem BirkhoffGlobalSection.radial_characteristic_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_radial_characteristic_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_radial_characteristic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.radial_contact_exterior_pullback :
∀ (a : Phase → ℝ) (u v w : Phase)
    (ha : DifferentiableAt ℝ a u),
    fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x w) u v -
      fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x v) u w =
    -phaseSymplecticForm
      (fderiv ℝ (fun x : Phase => a x • x) u v)
      (fderiv ℝ (fun x : Phase => a x • x) u w) := by sorry
