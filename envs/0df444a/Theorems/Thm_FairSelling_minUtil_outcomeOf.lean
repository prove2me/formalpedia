-- Prove2me | Theorems.Thm_FairSelling_minUtil_outcomeOf
-- name    : FairSelling.minUtil_outcomeOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:17.645694+00:00
-- url     : https://prove2.me/theorems/d9eac2b3-b996-4737-ba71-f867cf702d2e
-- title:
--   Fair Selling: min Util outcome Of
-- statement:
--   The Fair Selling construction uses the min Util outcome Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L70-L71
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L70-L71

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.minUtil_outcomeOf (v : G → ℝ) (assign : G → Option (Fin n)) (m : Fin n → ℝ) :
    minUtil v (outcomeOf assign m) = minUtilData v assign m := by sorry
