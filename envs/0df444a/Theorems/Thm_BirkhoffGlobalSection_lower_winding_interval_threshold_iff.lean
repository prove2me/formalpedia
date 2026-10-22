-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_lower_winding_interval_threshold_iff
-- name    : BirkhoffGlobalSection.lower_winding_interval_threshold_iff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:14:47.905999+00:00
-- url     : https://prove2.me/theorems/bf8d5e18-6c76-48d3-9fb2-2a1bb16b89f7
-- title:
--   Lower winding interval threshold iff
-- statement:
--   For a nonempty closed real interval of width below one, the ceiling sum minus one is at least 2k+1 exactly when its lower endpoint exceeds the integer k.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 1 of the Proved theorem BirkhoffGlobalSection.winding_arithmetic_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_winding_arithmetic_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_winding_arithmetic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.lower_winding_interval_threshold_iff :
∀ (a b : ℝ) (k : ℤ)
    (hab : a ≤ b) (hwidth : b - a < 1),
    2 * k + 1 ≤ Int.ceil a + Int.ceil b - 1 ↔ (k : ℝ) < a := by sorry
