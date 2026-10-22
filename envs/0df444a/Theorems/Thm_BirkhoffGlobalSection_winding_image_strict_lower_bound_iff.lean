-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_winding_image_strict_lower_bound_iff
-- name    : BirkhoffGlobalSection.winding_image_strict_lower_bound_iff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:51:31.321985+00:00
-- url     : https://prove2.me/theorems/88c2d1de-e452-4c21-88f7-9d2f492ef2e9
-- title:
--   Winding image strict lower bound iff
-- statement:
--   When a function's image over [0,2π] is exactly a nonempty closed interval [a,b], all of those values exceed a threshold c exactly when a exceeds c.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 6 of the Proved theorem BirkhoffGlobalSection.contact_winding_interval_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_winding_interval_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_winding_interval_bundle

open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology

set_option maxHeartbeats 800000
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.winding_image_strict_lower_bound_iff :
∀ (d : ℝ → ℝ) (a b c : ℝ)
    (hab : a ≤ b) (himage : d '' Icc 0 (2 * Real.pi) = Icc a b),
    (∀ s ∈ Icc 0 (2 * Real.pi), c < d s) ↔ c < a := by sorry
