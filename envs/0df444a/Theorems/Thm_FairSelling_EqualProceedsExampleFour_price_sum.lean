-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleFour_price_sum
-- name    : FairSelling.EqualProceedsExampleFour.price_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:35.675933+00:00
-- url     : https://prove2.me/theorems/05277757-6c28-408c-bf23-10349e42bbf9
-- title:
--   Equal Proceeds Example Four: price sum
-- statement:
--   The Equal Proceeds Example Four construction uses the price sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L226-L227
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L226-L227

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleFour
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleFour.price_sum (S : Finset (Fin (N + 2))) : ∑ g ∈ S, price N g = (S.card : ℝ) := by sorry
