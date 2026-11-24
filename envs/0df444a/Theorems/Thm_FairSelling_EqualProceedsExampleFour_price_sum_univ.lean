-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleFour_price_sum_univ
-- name    : FairSelling.EqualProceedsExampleFour.price_sum_univ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:32:20.55293+00:00
-- url     : https://prove2.me/theorems/c70de5cf-48df-4c8a-bb81-6cbc016085cb
-- title:
--   Equal Proceeds Example Four: price sum univ
-- statement:
--   The Equal Proceeds Example Four construction uses the price sum univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L223-L224
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L223-L224

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleFour
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleFour.price_sum_univ : ∑ g : Fin (N + 2), price N g = ((N : ℝ) + 2) := by sorry
