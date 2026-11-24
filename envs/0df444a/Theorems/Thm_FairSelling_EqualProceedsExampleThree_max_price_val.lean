-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleThree_max_price_val
-- name    : FairSelling.EqualProceedsExampleThree.max_price_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:23:42.664817+00:00
-- url     : https://prove2.me/theorems/684c3e61-c52d-4e1e-af04-27887990727f
-- title:
--   Equal Proceeds Example Three: max price val
-- statement:
--   The Equal Proceeds Example Three construction uses the max price val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L83-L84
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L83-L84

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleThree.max_price_val (g : Fin (N + 1)) : max (price N g) (val N g) = 1 := by sorry
