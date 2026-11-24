-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleFour_outSellAll_equalProceeds
-- name    : FairSelling.EqualProceedsExampleFour.outSellAll_equalProceeds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:24:58.456558+00:00
-- url     : https://prove2.me/theorems/2a482ee6-891d-49f1-b078-980aa4ee5576
-- title:
--   Equal Proceeds Example Four: out Sell All equal Proceeds
-- statement:
--   The Equal Proceeds Example Four construction uses the out Sell All equal Proceeds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L248-L251
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L248-L251

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleFour
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleFour.outSellAll_equalProceeds : (outSellAll N).EqualProceeds (price N) := by sorry
