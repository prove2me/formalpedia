-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleFour_val_zero
-- name    : FairSelling.EqualProceedsExampleFour.val_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:50:33.621683+00:00
-- url     : https://prove2.me/theorems/c0790b2a-a3f0-41a5-b58c-ba6474b2fd4c
-- title:
--   Equal Proceeds Example Four: val zero
-- statement:
--   The Equal Proceeds Example Four construction uses the val zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L288-L289
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L288-L289

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleFour
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleFour.val_zero (L : ℝ) : val N L 0 = fun _ => 1 / L := by sorry
