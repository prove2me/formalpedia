-- Prove2me | Theorems.Thm_FairSelling_swapOutcome_valid
-- name    : FairSelling.swapOutcome_valid
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:52:00.913465+00:00
-- url     : https://prove2.me/theorems/4eee4b6d-4fe4-441f-86ed-aafcd308a52d
-- title:
--   Fair Selling: swap Outcome valid
-- statement:
--   The Fair Selling construction uses the swap Outcome valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L216-L222
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L216-L222

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G] [DecidableEq G]

theorem FairSelling.swapOutcome_valid (p : G → ℝ) (o : Outcome G 2) (h : o.Valid p) :
    (swapOutcome o).Valid p := by sorry
