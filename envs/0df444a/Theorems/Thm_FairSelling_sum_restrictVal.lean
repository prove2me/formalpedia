-- Prove2me | Theorems.Thm_FairSelling_sum_restrictVal
-- name    : FairSelling.sum_restrictVal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:54:05.093687+00:00
-- url     : https://prove2.me/theorems/c590f2cb-79e5-4b54-b375-e93cfa898bab
-- title:
--   Fair Selling: sum restrict Val
-- statement:
--   Summing a restricted function over a set is summing the original over the intersection.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L65-L69
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L65-L69

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]

theorem FairSelling.sum_restrictVal (R : Finset G) (w : G → ℝ) (s : Finset G) :
    ∑ g ∈ s, restrictVal R w g = ∑ g ∈ s ∩ R, w g := by sorry
