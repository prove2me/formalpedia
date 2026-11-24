-- Prove2me | Theorems.Thm_FairSelling_vbarSum_sdiff
-- name    : FairSelling.vbarSum_sdiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:11:42.101021+00:00
-- url     : https://prove2.me/theorems/4704aa23-694d-4661-a980-382a717bae08
-- title:
--   Fair Selling: vbar Sum sdiff
-- statement:
--   The Fair Selling construction uses the vbar Sum sdiff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L201-L203
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L201-L203

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]

theorem FairSelling.vbarSum_sdiff (w p : G → ℝ) {X Y : Finset G} (h : Y ⊆ X) :
    vbarSum w p (X \ Y) = vbarSum w p X - vbarSum w p Y := by sorry
