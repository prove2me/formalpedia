-- Prove2me | Theorems.Thm_FairSelling_config_merged_ge_one
-- name    : FairSelling.config_merged_ge_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:59.441396+00:00
-- url     : https://prove2.me/theorems/1918944d-bfe9-474d-b913-07a9d636275e
-- title:
--   Fair Selling: config merged ge one
-- statement:
--   A cruder bound for the merged bundle: it contains one of the two parts.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean#L92-L104
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean#L92-L104

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_ConfigSplit
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {A : Fin 3 → Finset G} {s : Finset G} {q : Fin 3 → ℝ} {r : ℝ}

theorem FairSelling.config_merged_ge_one (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hcfg : ConfigN 3 w p r A s q)
    (X : Finset G) {j' j'' k : Fin 3} (hk : k = j' ∨ k = j'') :
    r - q k - vbarSum w p (A k ∩ X) ≤ vbarSum w p ((A j' ∪ A j'') \ X) := by sorry
