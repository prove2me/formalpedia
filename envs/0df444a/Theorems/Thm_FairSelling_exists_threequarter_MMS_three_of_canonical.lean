-- Prove2me | Theorems.Thm_FairSelling_exists_threequarter_MMS_three_of_canonical
-- name    : FairSelling.exists_threequarter_MMS_three_of_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:27.954805+00:00
-- url     : https://prove2.me/theorems/29a3c48a-b9b1-4151-b9e2-d043dd633f49
-- title:
--   Fair Selling: exists threequarter MMS three of canonical
-- statement:
--   **The `n = 3`, `3/4`-MMS theorem, from a strictly canonical partition and Lemma 4.**  Only
--   the residual case of Lemma 4 (`LemmaFourCashSold`, the sale of a single good the agent values
--   above its market price) is assumed; every other case is proved.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L843-L853
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L843-L853

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

theorem FairSelling.exists_threequarter_MMS_three_of_canonical (hL4 : LemmaFourCashSold G)
    (v : Fin 3 → G → ℝ) (p : G → ℝ) (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ i g, vbar (v i) p g < (3 / 4 : ℝ) * MMS 3 (v i) p)
    (a : Fin 3) (hmax : ∀ i, MMS 3 (v i) p ≤ MMS 3 (v a) p)
    (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (lo : Fin 3)
    (hcan : IsCanonicalStrict (v a) p ((3 / 4 : ℝ) * MMS 3 (v a) p) kept sold money lo) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by sorry
