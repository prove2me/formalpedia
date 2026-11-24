-- Prove2me | Theorems.Thm_FairSelling_lemmaFourCash_of_sold
-- name    : FairSelling.lemmaFourCash_of_sold
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:44:15.845393+00:00
-- url     : https://prove2.me/theorems/348a133c-55e8-4806-86a7-40969765aecb
-- title:
--   Fair Selling: lemma Four Cash of sold
-- statement:
--   **Lemma 4 reduces to its residual (singleton) case.**  A pure bundle is handled by the
--   value-counting argument.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L653-L669
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L653-L669

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.lemmaFourCash_of_sold (h : LemmaFourCashSold G) : LemmaFourCash G := by sorry
