-- Prove2me | Theorems.Thm_FairSelling_not_lemmaFourCashNoPrice
-- name    : FairSelling.not_lemmaFourCashNoPrice
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:06:47.11512+00:00
-- url     : https://prove2.me/theorems/931e0af9-8c8c-4efd-8e6b-4415839dfd52
-- title:
--   Fair Selling: not lemma Four Cash No Price
-- statement:
--   **The price condition in Lemma 4 cannot be dropped.**  Without the requirement that a
--   force-sold good is expensive (`p f ≥ MMS / 4`, condition 1 of the manuscript's canonical
--   partitions), the cash-aware Lemma 4 is false.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourNecessity.lean#L162-L187
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourNecessity.lean#L162-L187

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_LemmaFourNecessity
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open LemmaFourCounterexample

theorem FairSelling.not_lemmaFourCashNoPrice : ¬ LemmaFourCashNoPrice (Fin 6) := by sorry
