-- Prove2me | Theorems.Thm_FairSelling_vbarSum_sold_le
-- name    : FairSelling.vbarSum_sold_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:11.627143+00:00
-- url     : https://prove2.me/theorems/9fc07953-e7d9-49c6-b3ae-ad9c73a0cb6b
-- title:
--   Fair Selling: vbar Sum sold le
-- statement:
--   Small goods make the force-sold set cheap.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L439-L453
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L439-L453

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

theorem FairSelling.vbarSum_sold_le (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (S : Finset G) (hcard : S.card ≤ 2)
    (hsmall : ∀ g, vbar w p g < (3 / 4 : ℝ) * MMS 3 w p) :
    vbarSum w p S ≤ 2 * ((3 / 4 : ℝ) * MMS 3 w p) := by sorry
