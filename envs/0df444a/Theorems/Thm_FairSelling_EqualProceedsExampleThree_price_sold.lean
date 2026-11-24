-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleThree_price_sold
-- name    : FairSelling.EqualProceedsExampleThree.price_sold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:24.804727+00:00
-- url     : https://prove2.me/theorems/7de61c7d-dc4c-4942-94c8-a191512bdacc
-- title:
--   Equal Proceeds Example Three: price sold
-- statement:
--   The Equal Proceeds Example Three construction uses the price sold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L86-L87
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L86-L87

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleThree.price_sold : ∑ g ∈ ({0} : Finset (Fin (N + 1))), price N g = 1 := by sorry
