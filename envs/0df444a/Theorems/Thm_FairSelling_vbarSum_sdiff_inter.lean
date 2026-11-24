-- Prove2me | Theorems.Thm_FairSelling_vbarSum_sdiff_inter
-- name    : FairSelling.vbarSum_sdiff_inter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:44:49.314543+00:00
-- url     : https://prove2.me/theorems/a1d26f5f-dc33-4524-9128-3d47e43172f3
-- title:
--   Fair Selling: vbar Sum sdiff inter
-- statement:
--   Removing a set from a bundle removes exactly the value of the intersection.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean#L31-L35
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean#L31-L35

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_ConfigSplit
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]

theorem FairSelling.vbarSum_sdiff_inter (w p : G → ℝ) (Y X : Finset G) :
    vbarSum w p (Y \ X) = vbarSum w p Y - vbarSum w p (Y ∩ X) := by sorry
