-- Prove2me | Theorems.Thm_FairSelling_four_thr_le_vbarSum_univ
-- name    : FairSelling.four_thr_le_vbarSum_univ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:34:01.540717+00:00
-- url     : https://prove2.me/theorems/cdaa6841-e07d-41c4-bb87-69285f35e5de
-- title:
--   Fair Selling: four thr le vbar Sum univ
-- statement:
--   `4 · (3/4 · MMS) = 3 · MMS ≤ v̄(all goods)`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L378-L381
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L378-L381

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

theorem FairSelling.four_thr_le_vbarSum_univ (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g) :
    4 * ((3 / 4 : ℝ) * MMS 3 w p) ≤ vbarSum w p Finset.univ := by sorry
