-- Prove2me | Theorems.Thm_FairSelling_util_dropCashOutcome
-- name    : FairSelling.util_dropCashOutcome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:05:53.39847+00:00
-- url     : https://prove2.me/theorems/8124b9da-66e1-4a28-ad60-4b521e8d0969
-- title:
--   Fair Selling: util drop Cash Outcome
-- statement:
--   The Fair Selling construction uses the util drop Cash Outcome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L88-L93
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L88-L93

import Mathlib
import Definitions.Def_RequestProject_ThreeAgentCash
import Definitions.Def_RequestProject_ThreeAgentCashComposition
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.util_dropCashOutcome (R : Finset G) (w : G → ℝ)
    (o : Outcome (Option G) 2) (i : Fin 2) :
    util (restrictVal R w) (dropCashOutcome o) i = util (cashVal R w) o i := by sorry
