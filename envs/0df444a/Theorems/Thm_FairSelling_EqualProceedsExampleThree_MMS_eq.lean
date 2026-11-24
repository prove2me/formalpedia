-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleThree_MMS_eq
-- name    : FairSelling.EqualProceedsExampleThree.MMS_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:24:37.649473+00:00
-- url     : https://prove2.me/theorems/eb243ce8-976b-4140-9948-a4e5a1b2d76a
-- title:
--   Equal Proceeds Example Three: MMS eq
-- statement:
--   **The unconstrained maximin share of Example 3 is `1`.**
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L155-L161
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L155-L161

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleThree.MMS_eq : MMS (N + 1) (val N) (price N) = 1 := by sorry
