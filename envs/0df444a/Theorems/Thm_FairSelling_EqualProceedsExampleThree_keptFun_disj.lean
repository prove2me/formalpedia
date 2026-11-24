-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleThree_keptFun_disj
-- name    : FairSelling.EqualProceedsExampleThree.keptFun_disj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:50:20.545687+00:00
-- url     : https://prove2.me/theorems/3ea9e198-bd1d-4028-9982-de434d17516e
-- title:
--   Equal Proceeds Example Three: kept Fun disj
-- statement:
--   The Equal Proceeds Example Three construction uses the kept Fun disj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L89-L92
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L89-L92

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleThree.keptFun_disj (j k : Fin (N + 1)) (hjk : j ≠ k) :
    Disjoint (keptFun N j) (keptFun N k) := by sorry
