-- Prove2me | Theorems.Thm_FairSelling_LemmaFourCounterexample_no_two_bundles
-- name    : FairSelling.LemmaFourCounterexample.no_two_bundles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:09:23.234735+00:00
-- url     : https://prove2.me/theorems/00306d6d-9282-414f-b795-ad8fcc4b5659
-- title:
--   Lemma Four Counterexample: no two bundles
-- statement:
--   The combinatorial heart: no two disjoint bundles of the remaining goods are both worth
--   more than `37`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourNecessity.lean#L125-L127
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourNecessity.lean#L125-L127

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_LemmaFourNecessity
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.LemmaFourCounterexample

theorem FairSelling.LemmaFourCounterexample.no_two_bundles : ∀ A B : Finset (Option (Fin 6)), Disjoint A B →
    (∑ x ∈ A, cwn x) ≤ 37 ∨ (∑ x ∈ B, cwn x) ≤ 37 := by sorry
