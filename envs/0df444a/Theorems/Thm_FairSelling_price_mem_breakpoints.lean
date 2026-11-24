-- Prove2me | Theorems.Thm_FairSelling_price_mem_breakpoints
-- name    : FairSelling.price_mem_breakpoints
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:52:45.756435+00:00
-- url     : https://prove2.me/theorems/0d41c1be-3281-4b2f-b666-eb73d08e3a0d
-- title:
--   Fair Selling: price mem breakpoints
-- statement:
--   The Fair Selling construction uses the price mem breakpoints property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L347-L350
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L347-L350

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.price_mem_breakpoints (v p : G → ℝ) (g : G) : p g ∈ breakpoints v p := by sorry
