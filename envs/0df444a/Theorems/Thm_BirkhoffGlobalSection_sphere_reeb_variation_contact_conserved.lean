-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_sphere_reeb_variation_contact_conserved
-- name    : BirkhoffGlobalSection.sphere_reeb_variation_contact_conserved
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:45:26.266993+00:00
-- url     : https://prove2.me/theorems/61b287b0-2c45-4ae3-9bcf-e9fb66e8c25d
-- title:
--   Sphere reeb variation contact conserved
-- statement:
--   For supplied sphere Reeb trajectories and variational solutions, the weighted contact value of the variation is conserved when the weight is smooth and positive.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 4 of the Proved theorem BirkhoffGlobalSection.contact_variation_preservation_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_variation_preservation_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.sphere_reeb_variation_contact_conserved :
∀ (f : Phase → ℝ) (q v : ℝ → Phase)
    (hf : ∀ u ∈ unitThreeSphere, ContDiffAt ℝ ∞ f u ∧ 0 < f u)
    (hqS : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (sphereReebExtension f (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ (sphereReebExtension f) (q t) (v t)) t)
    (h0 : q 0 0 * v 0 0 + q 0 1 * v 0 1 + q 0 2 * v 0 2 + q 0 3 * v 0 3 = 0),
    ∀ t, f (q t) * phaseRadialContact (q t) (v t) =
      f (q 0) * phaseRadialContact (q 0) (v 0) := by sorry
