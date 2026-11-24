-- Prove2me | Theorems.Thm_FairSelling_LemmaFourCounterexample_wn_sum
-- name    : FairSelling.LemmaFourCounterexample.wn_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:08:40.724539+00:00
-- url     : https://prove2.me/theorems/be2dbe82-2ce8-42a0-90d6-6a50df022e87
-- title:
--   Lemma Four Counterexample: wn sum
-- statement:
--   The Lemma Four Counterexample construction uses the wn sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourNecessity.lean#L69-L69
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourNecessity.lean#L69-L69

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_LemmaFourNecessity
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.LemmaFourCounterexample

theorem FairSelling.LemmaFourCounterexample.wn_sum : ∑ g, wn g = 150 := by sorry
