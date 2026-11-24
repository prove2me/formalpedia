-- Prove2me | Theorems.Thm_FairSelling_LemmaFourCounterexample_vbarSum_univ
-- name    : FairSelling.LemmaFourCounterexample.vbarSum_univ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:08:51.497683+00:00
-- url     : https://prove2.me/theorems/33a67c6f-b71e-4071-b11a-b20af2a8b775
-- title:
--   Lemma Four Counterexample: vbar Sum univ
-- statement:
--   The Lemma Four Counterexample construction uses the vbar Sum univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourNecessity.lean#L75-L81
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourNecessity.lean#L75-L81

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_LemmaFourNecessity
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.LemmaFourCounterexample

theorem FairSelling.LemmaFourCounterexample.vbarSum_univ : vbarSum w p Finset.univ = 150 := by sorry
