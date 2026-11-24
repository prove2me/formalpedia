-- Prove2me | Theorems.Thm_FairSelling_config_two_parts_sdiff_ge
-- name    : FairSelling.config_two_parts_sdiff_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:44:58.026208+00:00
-- url     : https://prove2.me/theorems/eee2c01e-f9cb-4c3a-97c1-d3313b563349
-- title:
--   Fair Selling: config two parts sdiff ge
-- statement:
--   The value of the two merged surviving parts.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean#L80-L89
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean#L80-L89

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_ConfigSplit
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {A : Fin 3 → Finset G} {s : Finset G} {q : Fin 3 → ℝ} {r : ℝ}

theorem FairSelling.config_two_parts_sdiff_ge (w p : G → ℝ) (hcfg : ConfigN 3 w p r A s q) (X : Finset G)
    {j' j'' : Fin 3} (h : j' ≠ j'') :
    2 * r - q j' - q j'' - vbarSum w p ((A j' ∪ A j'') ∩ X)
      ≤ vbarSum w p ((A j' ∪ A j'') \ X) := by sorry
