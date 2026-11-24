-- Prove2me | Theorems.Thm_FairSelling_MMS2_cash_of_config_split
-- name    : FairSelling.MMS2_cash_of_config_split
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:44:57.022867+00:00
-- url     : https://prove2.me/theorems/866ca683-5538-47d7-8b56-0023f026d470
-- title:
--   Fair Selling: MMS2 cash of config split
-- statement:
--   **Rebuilding two bundles from a configuration.**  Keep the part `A j` on its own, merge the
--   other two parts, sell whatever survives of the force-sold set, and use the banked cash `c`
--   together with the proceeds to top both bundles up to `τ`.  The only thing to check is that the
--   money suffices.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean#L169-L202
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean#L169-L202

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_ConfigSplit
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {A : Fin 3 → Finset G} {s : Finset G} {q : Fin 3 → ℝ} {r : ℝ}

theorem FairSelling.MMS2_cash_of_config_split (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hcfg : ConfigN 3 w p r A s q) (X : Finset G) (c τ : ℝ) (hc : 0 ≤ c)
    {j j' j'' : Fin 3} (h1 : j ≠ j') (h2 : j ≠ j'')
    (hbudget : max 0 (τ - vbarSum w p (A j \ X)) + max 0 (τ - vbarSum w p ((A j' ∪ A j'') \ X))
      ≤ c + ∑ g ∈ s \ X, p g) :
    τ ≤ MMS 2 (cashVal (Finset.univ \ X) w) (cashPrice (Finset.univ \ X) p c) := by sorry
