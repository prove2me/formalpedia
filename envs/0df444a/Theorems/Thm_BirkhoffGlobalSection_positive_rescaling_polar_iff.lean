-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_positive_rescaling_polar_iff
-- name    : BirkhoffGlobalSection.positive_rescaling_polar_iff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:43:22.47676+00:00
-- url     : https://prove2.me/theorems/d848a4aa-a9e0-456b-a95b-738c1ddca213
-- title:
--   Positive rescaling polar iff
-- statement:
--   A plane vector and a positive scalar multiple admit positive-radius polar representations with exactly the same prescribed angle.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 6 of the Proved theorem BirkhoffGlobalSection.contact_frame_angle_disk_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_angle_disk_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.positive_rescaling_polar_iff :
∀ (p q : Plane) (a θ : ℝ)
    (ha : 0 < a) (hq : q = a • p),
    (∃ r : ℝ, 0 < r ∧ p = ![r * Real.cos θ, r * Real.sin θ]) ↔
    (∃ r : ℝ, 0 < r ∧ q = ![r * Real.cos θ, r * Real.sin θ]) := by sorry
