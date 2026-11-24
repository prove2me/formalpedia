-- Prove2me | Theorems.Thm_FairSelling_sum_le_vbarSum
-- name    : FairSelling.sum_le_vbarSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:30:22.773367+00:00
-- url     : https://prove2.me/theorems/f2b9a6b7-fee4-42d1-ab68-e97bb72d27c7
-- title:
--   Fair Selling: sum le vbar Sum
-- statement:
--   Plain valuation of a bundle never exceeds its `v̄`-valuation.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L35-L36
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L35-L36

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G] [DecidableEq G]

theorem FairSelling.sum_le_vbarSum (w p : G → ℝ) (A : Finset G) : ∑ g ∈ A, w g ≤ vbarSum w p A := by sorry
