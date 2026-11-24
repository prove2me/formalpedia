-- Prove2me | Theorems.Thm_FairSelling_config_sold_sdiff
-- name    : FairSelling.config_sold_sdiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:45:11.651193+00:00
-- url     : https://prove2.me/theorems/6829f238-f0e6-485d-b309-c1c76c999aec
-- title:
--   Fair Selling: config sold sdiff
-- statement:
--   The proceeds of the force-sold goods that survive.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean#L107-L111
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean#L107-L111

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_ConfigSplit
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {A : Fin 3 → Finset G} {s : Finset G} {q : Fin 3 → ℝ} {r : ℝ}

theorem FairSelling.config_sold_sdiff (w p : G → ℝ) (hcfg : ConfigN 3 w p r A s q) (X : Finset G) :
    ∑ g ∈ s \ X, p g = (∑ i, q i) - ∑ g ∈ s ∩ X, p g := by sorry
