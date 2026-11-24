-- Prove2me | Theorems.Thm_FairSelling_fin3_others
-- name    : FairSelling.fin3_others
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:23:18.206903+00:00
-- url     : https://prove2.me/theorems/bc67a6fb-e2c5-4bda-95bf-1a25cfe539f7
-- title:
--   Fair Selling: fin3 others
-- statement:
--   The three indices of `Fin 3` other than a given one.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L315-L319
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L315-L319

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

theorem FairSelling.fin3_others (k : Fin 3) : ∃ j j' : Fin 3, j ≠ k ∧ j' ≠ k ∧ j ≠ j' := by sorry
