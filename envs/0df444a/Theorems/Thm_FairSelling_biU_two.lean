-- Prove2me | Theorems.Thm_FairSelling_biU_two
-- name    : FairSelling.biU_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:51:50.984852+00:00
-- url     : https://prove2.me/theorems/86b315fc-a972-4acf-9634-7852739bb247
-- title:
--   Fair Selling: bi U two
-- statement:
--   The Fair Selling construction uses the bi U two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L172-L174
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L172-L174

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]

theorem FairSelling.biU_two (A : Fin 2 → Finset G) : Finset.univ.biUnion A = A 0 ∪ A 1 := by sorry
