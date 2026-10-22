-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_radial_normalize_regular
-- name    : BirkhoffGlobalSection.radial_normalize_regular
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:16:13.589466+00:00
-- url     : https://prove2.me/theorems/73732bb6-9564-4c4e-a5d4-ec3e4c1ded95
-- title:
--   Radial normalize regular
-- statement:
--   Radial normalization is smooth at a phase point with positive squared radius, and its value lies on the unit three-sphere.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 1 of the Proved theorem BirkhoffGlobalSection.smooth_sphere_reeb_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_smooth_sphere_reeb_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_smooth_sphere_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.radial_normalize_regular :
∀ (x : Phase) (hx : 0 < zNormSq x + wNormSq x),
    ContDiffAt ℝ ∞ radialNormalize x ∧ radialNormalize x ∈ unitThreeSphere := by sorry
