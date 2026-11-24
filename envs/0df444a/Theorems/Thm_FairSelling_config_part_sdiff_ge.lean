-- Prove2me | Theorems.Thm_FairSelling_config_part_sdiff_ge
-- name    : FairSelling.config_part_sdiff_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:34:16.845607+00:00
-- url     : https://prove2.me/theorems/b438beae-6699-4a3b-8995-cf9c6ab06b94
-- title:
--   Fair Selling: config part sdiff ge
-- statement:
--   The value of a single surviving part.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean#L72-L77
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean#L72-L77

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_ConfigSplit
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {A : Fin 3 → Finset G} {s : Finset G} {q : Fin 3 → ℝ} {r : ℝ}

theorem FairSelling.config_part_sdiff_ge (w p : G → ℝ) (hcfg : ConfigN 3 w p r A s q) (X : Finset G)
    (j : Fin 3) :
    r - q j - vbarSum w p (A j ∩ X) ≤ vbarSum w p (A j \ X) := by sorry
