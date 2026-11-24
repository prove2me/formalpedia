-- Prove2me | Theorems.Thm_FairSelling_sum_price_le_vbarSum
-- name    : FairSelling.sum_price_le_vbarSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:37.573175+00:00
-- url     : https://prove2.me/theorems/0db86fc1-b825-4f72-9426-cce3e9d31a32
-- title:
--   Fair Selling: sum price le vbar Sum
-- statement:
--   Prices are dominated by `v̄`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean#L39-L41
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean#L39-L41

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_ConfigSplit
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G] [DecidableEq G]

theorem FairSelling.sum_price_le_vbarSum (w p : G → ℝ) (Y : Finset G) :
    ∑ g ∈ Y, p g ≤ vbarSum w p Y := by sorry
