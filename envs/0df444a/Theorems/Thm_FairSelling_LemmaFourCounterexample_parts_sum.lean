-- Prove2me | Theorems.Thm_FairSelling_LemmaFourCounterexample_parts_sum
-- name    : FairSelling.LemmaFourCounterexample.parts_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:08:59.454395+00:00
-- url     : https://prove2.me/theorems/0def66bb-9913-4381-9a6f-284a70043de1
-- title:
--   Lemma Four Counterexample: parts sum
-- statement:
--   The Lemma Four Counterexample construction uses the parts sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourNecessity.lean#L71-L71
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourNecessity.lean#L71-L71

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_LemmaFourNecessity
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.LemmaFourCounterexample

theorem FairSelling.LemmaFourCounterexample.parts_sum : ∀ j, ∑ g ∈ parts j, wn g = 50 := by sorry
