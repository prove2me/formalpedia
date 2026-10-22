-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_sphere_reeb_variation_contact
-- name    : BirkhoffGlobalSection.sphere_reeb_variation_contact
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:45:29.927986+00:00
-- url     : https://prove2.me/theorems/095be299-dcdc-46aa-b420-720e7f4cf9f1
-- title:
--   Sphere reeb variation contact
-- statement:
--   An initially zero-contact variational vector remains in the weighted contact kernel along a supplied sphere Reeb trajectory under the stated differential hypotheses.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 5 of the Proved theorem BirkhoffGlobalSection.contact_variation_preservation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_variation_preservation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.sphere_reeb_variation_contact :
∀ (f : Phase → ℝ) (q v : ℝ → Phase)
    (hf : ∀ u ∈ unitThreeSphere, ContDiffAt ℝ ∞ f u ∧ 0 < f u)
    (hqS : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (sphereReebExtension f (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ (sphereReebExtension f) (q t) (v t)) t)
    (h0 : q 0 0 * v 0 0 + q 0 1 * v 0 1 + q 0 2 * v 0 2 + q 0 3 * v 0 3 = 0)
    (hα0 : phaseRadialContact (q 0) (v 0) = 0),
    ∀ t, phaseRadialContact (q t) (v t) = 0 := by sorry
