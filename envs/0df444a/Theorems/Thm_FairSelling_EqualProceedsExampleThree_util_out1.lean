-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleThree_util_out1
-- name    : FairSelling.EqualProceedsExampleThree.util_out1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:24:21.718224+00:00
-- url     : https://prove2.me/theorems/b1f9874f-030a-4023-a630-27316ab3b878
-- title:
--   Equal Proceeds Example Three: util out1
-- statement:
--   The Equal Proceeds Example Three construction uses the util out1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L142-L144
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L142-L144

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleThree.util_out1 (j : Fin (N + 1)) : util (val N) (out1 N) j = 1 := by sorry
