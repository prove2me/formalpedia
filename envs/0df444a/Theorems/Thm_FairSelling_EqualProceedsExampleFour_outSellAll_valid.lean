-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleFour_outSellAll_valid
-- name    : FairSelling.EqualProceedsExampleFour.outSellAll_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:24:53.21201+00:00
-- url     : https://prove2.me/theorems/9fa54a3d-033c-40f0-9cce-23ec3ad94098
-- title:
--   Equal Proceeds Example Four: out Sell All valid
-- statement:
--   The Equal Proceeds Example Four construction uses the out Sell All valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L241-L246
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L241-L246

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleFour
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleFour.outSellAll_valid : (outSellAll N).Valid (price N) := by sorry
