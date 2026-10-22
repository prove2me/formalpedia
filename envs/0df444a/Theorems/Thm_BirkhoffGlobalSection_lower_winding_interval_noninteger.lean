-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_lower_winding_interval_noninteger
-- name    : BirkhoffGlobalSection.lower_winding_interval_noninteger
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:14:51.804698+00:00
-- url     : https://prove2.me/theorems/42e26e2a-0558-4f00-94fa-2a8f62f31584
-- title:
--   Lower winding interval noninteger
-- statement:
--   When both endpoints lie strictly between consecutive integers k and k+1, the ceiling sum minus one equals 2k+1.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 3 of the Proved theorem BirkhoffGlobalSection.winding_arithmetic_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_winding_arithmetic_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_winding_arithmetic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.lower_winding_interval_noninteger :
∀ (a b : ℝ) (k : ℤ)
    (ha : (k : ℝ) < a) (hab : a ≤ b) (hb : b < (k : ℝ) + 1),
    Int.ceil a + Int.ceil b - 1 = 2 * k + 1 := by sorry
