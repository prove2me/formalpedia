-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_area_preserving_polar_winding_width
-- name    : BirkhoffGlobalSection.area_preserving_polar_winding_width
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:51:38.9001+00:00
-- url     : https://prove2.me/theorems/82580318-6cd7-4182-b446-d8beeb52b111
-- title:
--   Area preserving polar winding width
-- statement:
--   For the supplied normalized positive polar data of a real-linear area-preserving plane action, its directional winding image is an attained closed interval of width strictly below one half, with the displayed threshold characterization.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 6 of the Proved theorem BirkhoffGlobalSection.contact_winding_width_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_winding_width_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_winding_width_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.area_preserving_polar_winding_width :
∀ (A : ℝ → Plane → Plane)
    (ρ θ : ℝ × ℝ → ℝ) (hθ : Continuous θ) (hρ : ∀ x, 0 < ρ x)
    (hθ0 : ∀ s, θ (0, s) = s)
    (hpolar : ∀ t s, A t ![Real.cos s, Real.sin s] =
      ![ρ (t, s) * Real.cos (θ (t, s)), ρ (t, s) * Real.sin (θ (t, s))])
    (harea : ∀ t p r, A t p 0 * A t r 1 - A t p 1 * A t r 0 = p 0 * r 1 - p 1 * r 0)
    (hneg : ∀ t p, A t (-p) = -(A t p)) (T a b : ℝ) (hab : a ≤ b)
    (himage : (fun s => (θ (T, s) - s) / (2 * Real.pi)) '' Icc 0 (2 * Real.pi) = Icc a b),
    b - a < 1 / 2 := by sorry
