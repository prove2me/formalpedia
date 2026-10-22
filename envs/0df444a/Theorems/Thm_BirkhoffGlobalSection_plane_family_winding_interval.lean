-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_plane_family_winding_interval
-- name    : BirkhoffGlobalSection.plane_family_winding_interval
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:51:27.381304+00:00
-- url     : https://prove2.me/theorems/df2113fe-1251-48fd-ab7e-d8c574e126f6
-- title:
--   Plane family winding interval
-- statement:
--   For a jointly continuous real angle family at a fixed time, the normalized increments over initial angles in [0,2π] form a nonempty closed interval with both endpoints attained.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 5 of the Proved theorem BirkhoffGlobalSection.contact_winding_interval_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_winding_interval_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_winding_interval_bundle

open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology

set_option maxHeartbeats 800000
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.plane_family_winding_interval :
∀ (θ : ℝ × ℝ → ℝ) (hθ : Continuous θ) (T : ℝ),
    ∃ a b : ℝ, a ≤ b ∧
      (fun s => (θ (T, s) - s) / (2 * Real.pi)) '' Icc 0 (2 * Real.pi) = Icc a b ∧
      (∃ s ∈ Icc 0 (2 * Real.pi), (θ (T, s) - s) / (2 * Real.pi) = a) ∧
      (∃ s ∈ Icc 0 (2 * Real.pi), (θ (T, s) - s) / (2 * Real.pi) = b) := by sorry
