-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_lower_winding_interval_left_stable
-- name    : BirkhoffGlobalSection.lower_winding_interval_left_stable
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:15:11.700224+00:00
-- url     : https://prove2.me/theorems/7b374d69-92e0-45f6-b5aa-8c6c6539ce5b
-- title:
--   Lower winding interval left stable
-- statement:
--   For any two real endpoints, their ceiling sum minus one is unchanged when both are shifted left by every sufficiently small positive amount.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 7 of the Proved theorem BirkhoffGlobalSection.winding_arithmetic_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_winding_arithmetic_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_winding_arithmetic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.lower_winding_interval_left_stable :
∀ (a b : ℝ),
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      Int.ceil (a - ε) + Int.ceil (b - ε) - 1 = Int.ceil a + Int.ceil b - 1 := by sorry
