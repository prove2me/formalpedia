-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_plane_positive_polar_unique
-- name    : BirkhoffGlobalSection.plane_positive_polar_unique
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:49:54.474984+00:00
-- url     : https://prove2.me/theorems/3e8afcb8-e5d3-467e-8eca-065af9de064d
-- title:
--   Plane positive polar unique
-- statement:
--   Two positive-radius polar representations of the same plane vector have the same radius, cosine and sine.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 4 of the Proved theorem BirkhoffGlobalSection.contact_angular_lift_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_angular_lift_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_angular_lift_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.plane_positive_polar_unique :
∀ (v : Plane) (ρ σ θ ψ : ℝ)
    (hρ : 0 < ρ) (hσ : 0 < σ)
    (hθ : v = ![ρ * Real.cos θ, ρ * Real.sin θ])
    (hψ : v = ![σ * Real.cos ψ, σ * Real.sin ψ]),
    ρ = σ ∧ Real.cos θ = Real.cos ψ ∧ Real.sin θ = Real.sin ψ := by sorry
