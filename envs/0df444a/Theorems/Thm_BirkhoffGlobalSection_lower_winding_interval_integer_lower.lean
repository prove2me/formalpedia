-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_lower_winding_interval_integer_lower
-- name    : BirkhoffGlobalSection.lower_winding_interval_integer_lower
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:15:01.701421+00:00
-- url     : https://prove2.me/theorems/fd708e22-fc8b-48f7-b43e-08d9eb9df7ef
-- title:
--   Lower winding interval integer lower
-- statement:
--   For an interval of width below one whose lower endpoint is k and upper endpoint is above k, the ceiling sum minus one equals 2k.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 6 of the Proved theorem BirkhoffGlobalSection.winding_arithmetic_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_winding_arithmetic_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_winding_arithmetic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.lower_winding_interval_integer_lower :
∀ (b : ℝ) (k : ℤ)
    (hb : (k : ℝ) < b) (hwidth : b - (k : ℝ) < 1),
    Int.ceil (k : ℝ) + Int.ceil b - 1 = 2 * k := by sorry
