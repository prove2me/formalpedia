-- Prove2me | Theorems.Thm_FairSelling_disjoint_compl_of_subset
-- name    : FairSelling.disjoint_compl_of_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:06:41.73757+00:00
-- url     : https://prove2.me/theorems/fb54b0e7-5dd9-46a8-bff4-848837f67b8a
-- title:
--   Fair Selling: disjoint compl of subset
-- statement:
--   A set contained in `U` is disjoint from the complement of `U`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L370-L373
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L370-L373

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

theorem FairSelling.disjoint_compl_of_subset {Y U : Finset G} (hYU : Y ⊆ U) :
    Disjoint Y (Finset.univ \ U) := by sorry
