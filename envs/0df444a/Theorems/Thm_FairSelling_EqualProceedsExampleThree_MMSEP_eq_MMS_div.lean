-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleThree_MMSEP_eq_MMS_div
-- name    : FairSelling.EqualProceedsExampleThree.MMSEP_eq_MMS_div
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:32:16.400384+00:00
-- url     : https://prove2.me/theorems/b30946ce-54e6-494c-8737-b6dd4e1ae808
-- title:
--   Equal Proceeds Example Three: MMSEP eq MMS div
-- statement:
--   **Example 3**: the equal-proceeds maximin share is `1/n` times the unconstrained maximin
--   share.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L202-L204
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L202-L204

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleThree.MMSEP_eq_MMS_div :
    MMSEP (N + 1) (val N) (price N) = MMS (N + 1) (val N) (price N) / ((N : ℝ) + 1) := by sorry
