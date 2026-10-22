-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_radial_scale_contDiffAt
-- name    : BirkhoffGlobalSection.radial_scale_contDiffAt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:16:15.729446+00:00
-- url     : https://prove2.me/theorems/5931a24c-a54b-466d-9ab8-da2092b1c608
-- title:
--   Radial scale contDiffAt
-- statement:
--   At a nonzero phase point, smoothness of a scalar radial rescaling x ↦ a(x)x implies smoothness of its scalar factor a.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 4 of the Proved theorem BirkhoffGlobalSection.smooth_sphere_reeb_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_smooth_sphere_reeb_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_smooth_sphere_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.radial_scale_contDiffAt :
∀ (a : Phase → ℝ) (u : Phase) (hu : u ≠ 0)
    (hG : ContDiffAt ℝ ∞ (fun x : Phase => a x • x) u),
    ContDiffAt ℝ ∞ a u := by sorry
