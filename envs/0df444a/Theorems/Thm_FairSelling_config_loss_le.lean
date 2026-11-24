-- Prove2me | Theorems.Thm_FairSelling_config_loss_le
-- name    : FairSelling.config_loss_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:07:58.134771+00:00
-- url     : https://prove2.me/theorems/4b081c2a-cc20-4e7a-b69d-f88337112873
-- title:
--   Fair Selling: config loss le
-- statement:
--   The three parts and the force-sold set carve `X` up, so the losses they suffer add up to at
--   most the value of `X`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean#L115-L161
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean#L115-L161

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_ConfigSplit
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {A : Fin 3 → Finset G} {s : Finset G} {q : Fin 3 → ℝ} {r : ℝ}

theorem FairSelling.config_loss_le (w p : G → ℝ) (hcfg : ConfigN 3 w p r A s q) (X : Finset G)
    {j j' j'' : Fin 3} (h1 : j ≠ j') (h2 : j ≠ j'') (h3 : j' ≠ j'') :
    vbarSum w p (A j ∩ X) + vbarSum w p ((A j' ∪ A j'') ∩ X) + ∑ g ∈ s ∩ X, p g
      ≤ vbarSum w p X := by sorry
