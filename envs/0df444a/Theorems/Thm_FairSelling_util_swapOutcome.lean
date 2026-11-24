-- Prove2me | Theorems.Thm_FairSelling_util_swapOutcome
-- name    : FairSelling.util_swapOutcome
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:52:01.0233+00:00
-- url     : https://prove2.me/theorems/7daa34d4-e78c-42e0-821f-f28d0c9eef49
-- title:
--   Fair Selling: util swap Outcome
-- statement:
--   The Fair Selling construction uses the util swap Outcome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L212-L213
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L212-L213

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G] [DecidableEq G]

theorem FairSelling.util_swapOutcome (w : G → ℝ) (o : Outcome G 2) (j : Fin 2) :
    util w (swapOutcome o) j = util w o (Equiv.swap 0 1 j) := by sorry
