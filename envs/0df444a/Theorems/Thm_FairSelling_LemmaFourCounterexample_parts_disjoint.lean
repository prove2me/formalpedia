-- Prove2me | Theorems.Thm_FairSelling_LemmaFourCounterexample_parts_disjoint
-- name    : FairSelling.LemmaFourCounterexample.parts_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:08:42.725081+00:00
-- url     : https://prove2.me/theorems/0d0918ed-0ddb-4f2e-ad94-45fea0fca2a4
-- title:
--   Lemma Four Counterexample: parts disjoint
-- statement:
--   The Lemma Four Counterexample construction uses the parts disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourNecessity.lean#L73-L73
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourNecessity.lean#L73-L73

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_LemmaFourNecessity
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.LemmaFourCounterexample

theorem FairSelling.LemmaFourCounterexample.parts_disjoint : ∀ j k : Fin 3, j ≠ k → Disjoint (parts j) (parts k) := by sorry
