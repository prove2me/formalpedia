-- Prove2me | Theorems.Thm_FairSelling_LemmaFourCounterexample_MMS_two_le
-- name    : FairSelling.LemmaFourCounterexample.MMS_two_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:09:32.763605+00:00
-- url     : https://prove2.me/theorems/7b944991-2666-4f3e-a568-9196949bcb03
-- title:
--   Lemma Four Counterexample: MMS two le
-- statement:
--   The two-agent maximin share of the cash-augmented remainder is at most `37`, hence strictly
--   below the threshold `37.5`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourNecessity.lean#L131-L154
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourNecessity.lean#L131-L154

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_LemmaFourNecessity
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.LemmaFourCounterexample

theorem FairSelling.LemmaFourCounterexample.MMS_two_le : MMS 2 (cashVal R w) (cashPrice R p 0) ≤ 37 := by sorry
