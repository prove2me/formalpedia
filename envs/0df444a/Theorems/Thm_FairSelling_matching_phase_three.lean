-- Prove2me | Theorems.Thm_FairSelling_matching_phase_three
-- name    : FairSelling.matching_phase_three
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:07:07.74174+00:00
-- url     : https://prove2.me/theorems/8e6ae6eb-8d57-4307-936f-b6243528caaf
-- title:
--   Fair Selling: matching phase three
-- statement:
--   **The matching phase for three agents.**  Given the canonical partition proposed by the
--   partitioning agent `a` (in the manuscript's strict form) and no big goods, either the instance is
--   already completely solved, or we are in a single loss event.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L737-L838
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L737-L838

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

theorem FairSelling.matching_phase_three (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ i g, vbar (v i) p g < (3 / 4 : ℝ) * MMS 3 (v i) p)
    (a : Fin 3) (hmax : ∀ i, MMS 3 (v i) p ≤ MMS 3 (v a) p)
    (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (lo : Fin 3)
    (hcan : IsCanonicalStrict (v a) p ((3 / 4 : ℝ) * MMS 3 (v a) p) kept sold money lo) :
    (∃ o : Outcome G 3, o.Valid p ∧
        ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i)
      ∨ SingleLossConfig v p := by sorry
