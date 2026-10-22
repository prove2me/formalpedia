-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_area_preserving_polar_angle_gap
-- name    : BirkhoffGlobalSection.area_preserving_polar_angle_gap
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:51:30.297989+00:00
-- url     : https://prove2.me/theorems/716252a6-b484-40f8-8656-9c64ceef6bfa
-- title:
--   Area preserving polar angle gap
-- statement:
--   For the supplied normalized positive polar data of an area-preserving plane action, initially ordered directions separated by less than π keep their lifted angular separation strictly between zero and π.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 2 of the Proved theorem BirkhoffGlobalSection.contact_winding_width_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_winding_width_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_winding_width_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.area_preserving_polar_angle_gap :
∀ (A : ℝ → Plane → Plane)
    (ρ θ : ℝ × ℝ → ℝ) (hθ : Continuous θ)
    (hθ0 : ∀ s, θ (0, s) = s)
    (hpolar : ∀ t s, A t ![Real.cos s, Real.sin s] =
      ![ρ (t, s) * Real.cos (θ (t, s)), ρ (t, s) * Real.sin (θ (t, s))])
    (harea : ∀ t p r, A t p 0 * A t r 1 - A t p 1 * A t r 0 = p 0 * r 1 - p 1 * r 0)
    (s r : ℝ) (hsr : s < r) (hr : r - s < Real.pi),
    ∀ t, 0 < θ (t, r) - θ (t, s) ∧ θ (t, r) - θ (t, s) < Real.pi := by sorry
