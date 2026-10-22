-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_lower_winding_interval_ge_three_iff
-- name    : BirkhoffGlobalSection.lower_winding_interval_ge_three_iff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:14:54.963977+00:00
-- url     : https://prove2.me/theorems/4382fc95-1efa-4696-bdbc-6a20013efaf0
-- title:
--   Lower winding interval ge three iff
-- statement:
--   For a nonempty closed real interval of width below one, the ceiling sum minus one is at least three exactly when its lower endpoint exceeds one.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 2 of the Proved theorem BirkhoffGlobalSection.winding_arithmetic_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_winding_arithmetic_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_winding_arithmetic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.lower_winding_interval_ge_three_iff :
∀ (a b : ℝ)
    (hab : a ≤ b) (hwidth : b - a < 1),
    (3 : ℤ) ≤ Int.ceil a + Int.ceil b - 1 ↔ 1 < a := by sorry
