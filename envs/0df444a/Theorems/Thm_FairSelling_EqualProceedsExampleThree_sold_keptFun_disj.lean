-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleThree_sold_keptFun_disj
-- name    : FairSelling.EqualProceedsExampleThree.sold_keptFun_disj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:50:19.42881+00:00
-- url     : https://prove2.me/theorems/a410a2d9-88f5-416a-b87a-30f4272ac8aa
-- title:
--   Equal Proceeds Example Three: sold kept Fun disj
-- statement:
--   The Equal Proceeds Example Three construction uses the sold kept Fun disj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L94-L99
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L94-L99

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleThree.sold_keptFun_disj (j : Fin (N + 1)) :
    Disjoint ({0} : Finset (Fin (N + 1))) (keptFun N j) := by sorry
