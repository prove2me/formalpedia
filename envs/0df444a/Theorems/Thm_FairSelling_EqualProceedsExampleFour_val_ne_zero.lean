-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleFour_val_ne_zero
-- name    : FairSelling.EqualProceedsExampleFour.val_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:50:18.505808+00:00
-- url     : https://prove2.me/theorems/e8708912-c232-4f9a-b194-5969d61f61e2
-- title:
--   Equal Proceeds Example Four: val ne zero
-- statement:
--   The Equal Proceeds Example Four construction uses the val ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L291-L292
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L291-L292

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleFour
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleFour.val_ne_zero (L : ℝ) {i : Fin (N + 2)} (hi : i ≠ 0) : val N L i = fun _ => L := by sorry
