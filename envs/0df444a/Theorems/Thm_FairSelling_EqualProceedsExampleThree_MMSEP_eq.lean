-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleThree_MMSEP_eq
-- name    : FairSelling.EqualProceedsExampleThree.MMSEP_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:24:39.549597+00:00
-- url     : https://prove2.me/theorems/7cfb4859-2217-4da8-952e-d93ad0c1700c
-- title:
--   Equal Proceeds Example Three: MMSEP eq
-- statement:
--   **The equal-proceeds maximin share of Example 3 is `1/n`.**
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L164-L198
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L164-L198

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleThree.MMSEP_eq : MMSEP (N + 1) (val N) (price N) = 1 / ((N : ℝ) + 1) := by sorry
