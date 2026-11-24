-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleThree_util_out2
-- name    : FairSelling.EqualProceedsExampleThree.util_out2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:24:44.629363+00:00
-- url     : https://prove2.me/theorems/fa634961-7c04-4b90-b297-d8ceae3b8b78
-- title:
--   Equal Proceeds Example Three: util out2
-- statement:
--   The Equal Proceeds Example Three construction uses the util out2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L146-L152
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L146-L152

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleThree.util_out2 (j : Fin (N + 1)) : (1 : ℝ) / ((N : ℝ) + 1) ≤ util (val N) (out2 N) j := by sorry
