-- Prove2me | Theorems.Thm_FairSelling_vbarSum_union
-- name    : FairSelling.vbarSum_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:11:43.300848+00:00
-- url     : https://prove2.me/theorems/2bf91289-e983-4ea2-ac62-0a1b3c12297f
-- title:
--   Fair Selling: vbar Sum union
-- statement:
--   The Fair Selling construction uses the vbar Sum union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L39-L41
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L39-L41

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]

theorem FairSelling.vbarSum_union (w p : G → ℝ) {A B : Finset G} (h : Disjoint A B) :
    vbarSum w p (A ∪ B) = vbarSum w p A + vbarSum w p B := by sorry
