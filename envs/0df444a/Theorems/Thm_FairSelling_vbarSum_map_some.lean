-- Prove2me | Theorems.Thm_FairSelling_vbarSum_map_some
-- name    : FairSelling.vbarSum_map_some
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:06:04.517862+00:00
-- url     : https://prove2.me/theorems/e2d743dc-19a7-4d01-9638-96270100977d
-- title:
--   Fair Selling: vbar Sum map some
-- statement:
--   Bundles of ordinary goods inside the remainder keep their `v̄`-value in the cash-augmented
--   instance.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L78-L85
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L78-L85

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
omit [Fintype G]

theorem FairSelling.vbarSum_map_some (R : Finset G) (w p : G → ℝ) (c : ℝ) {C : Finset G} (hC : C ⊆ R) :
    vbarSum (cashVal R w) (cashPrice R p c) (C.map Function.Embedding.some)
      = vbarSum w p C := by sorry
