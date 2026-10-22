-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_lower_winding_interval_integer_upper
-- name    : BirkhoffGlobalSection.lower_winding_interval_integer_upper
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:15:04.803098+00:00
-- url     : https://prove2.me/theorems/730f8fb9-6df2-418d-ba23-368d9feb7d92
-- title:
--   Lower winding interval integer upper
-- statement:
--   For an interval of width below one whose upper endpoint is k and lower endpoint is at most k, the ceiling sum minus one equals 2k−1.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 5 of the Proved theorem BirkhoffGlobalSection.winding_arithmetic_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_winding_arithmetic_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_winding_arithmetic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.lower_winding_interval_integer_upper :
∀ (a : ℝ) (k : ℤ)
    (ha : a ≤ (k : ℝ)) (hwidth : (k : ℝ) - a < 1),
    Int.ceil a + Int.ceil (k : ℝ) - 1 = 2 * k - 1 := by sorry
