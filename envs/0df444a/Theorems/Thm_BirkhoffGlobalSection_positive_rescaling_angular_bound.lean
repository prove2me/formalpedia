-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_positive_rescaling_angular_bound
-- name    : BirkhoffGlobalSection.positive_rescaling_angular_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:43:34.375982+00:00
-- url     : https://prove2.me/theorems/4b42c0d6-94bf-45c6-bf68-3781de11f92d
-- title:
--   Positive rescaling angular bound
-- statement:
--   Pointwise positive rescaling of a plane curve preserves the stated universal continuous-polar-angle increment bound.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 7 of the Proved theorem BirkhoffGlobalSection.contact_frame_angle_disk_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_angle_disk_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.positive_rescaling_angular_bound :
∀ (p q : ℝ → Plane) (a : ℝ → ℝ) (T B : ℝ)
    (ha : ∀ t, 0 < a t) (heq : ∀ t, q t = a t • p t)
    (hbound : ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ p t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      B < θ T - θ 0),
    ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ q t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      B < θ T - θ 0 := by sorry
