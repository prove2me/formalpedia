-- Prove2me | Theorems.Thm_FairSelling_outcomeOf_cover
-- name    : FairSelling.outcomeOf_cover
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:51:35.454345+00:00
-- url     : https://prove2.me/theorems/02194e8f-5a13-406b-b521-c63a6bc2f2e3
-- title:
--   Fair Selling: outcome Of cover
-- statement:
--   Every good is either sold or kept by some part in an outcome of assignment form.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L186-L195
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L186-L195

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}

theorem FairSelling.outcomeOf_cover (assign : G → Option (Fin n)) (m : Fin n → ℝ) :
    (outcomeOf assign m).sold ∪ Finset.univ.biUnion (outcomeOf assign m).kept = Finset.univ := by sorry
