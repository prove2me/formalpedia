-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_lower_winding_interval_integer_crossing
-- name    : BirkhoffGlobalSection.lower_winding_interval_integer_crossing
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:14:57.648979+00:00
-- url     : https://prove2.me/theorems/886bcbce-9838-43ea-ae06-f86ae899ab1a
-- title:
--   Lower winding interval integer crossing
-- statement:
--   When an interval of width below one strictly crosses the integer k, the ceiling sum minus one equals 2k.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 4 of the Proved theorem BirkhoffGlobalSection.winding_arithmetic_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_winding_arithmetic_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_winding_arithmetic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.lower_winding_interval_integer_crossing :
∀ (a b : ℝ) (k : ℤ)
    (ha : a < (k : ℝ)) (hb : (k : ℝ) < b) (hwidth : b - a < 1),
    Int.ceil a + Int.ceil b - 1 = 2 * k := by sorry
