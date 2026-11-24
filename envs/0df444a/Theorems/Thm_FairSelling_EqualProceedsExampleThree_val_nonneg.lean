-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleThree_val_nonneg
-- name    : FairSelling.EqualProceedsExampleThree.val_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:49:05.339449+00:00
-- url     : https://prove2.me/theorems/74ab0dd6-04c1-4098-b5bf-db2ace69d8e2
-- title:
--   Equal Proceeds Example Three: val nonneg
-- statement:
--   The Equal Proceeds Example Three construction uses the val nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L77-L78
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L77-L78

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleThree.val_nonneg : ∀ g, 0 ≤ val N g := by sorry
