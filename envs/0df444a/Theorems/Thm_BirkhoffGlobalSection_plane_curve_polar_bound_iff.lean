-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_plane_curve_polar_bound_iff
-- name    : BirkhoffGlobalSection.plane_curve_polar_bound_iff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:50:28.019+00:00
-- url     : https://prove2.me/theorems/e5200573-4e78-4ee0-bc2e-8529775693aa
-- title:
--   Plane curve polar bound iff
-- statement:
--   For a continuous nonvanishing plane curve, a universal bound on increments of every continuous positive polar angle is equivalent to the corresponding bound for one continuous positive polar lift.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 8 of the Proved theorem BirkhoffGlobalSection.contact_angular_lift_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_angular_lift_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_angular_lift_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.plane_curve_polar_bound_iff :
∀ (v : ℝ → Plane) (hv : Continuous v)
    (hne : ∀ t, v t ≠ 0) (T L : ℝ),
    (∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ v t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      L < θ T - θ 0) ↔
    ∃ ρ θ : ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧ (∀ t, 0 < ρ t) ∧
      (∀ t, v t = ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)]) ∧ L < θ T - θ 0 := by sorry
