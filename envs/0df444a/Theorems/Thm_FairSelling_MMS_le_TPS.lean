-- Prove2me | Theorems.Thm_FairSelling_MMS_le_TPS
-- name    : FairSelling.MMS_le_TPS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:55.313221+00:00
-- url     : https://prove2.me/theorems/025fc7f2-fb91-48ef-9aca-96182e4b7470
-- title:
--   Fair Selling: MMS le TPS
-- statement:
--   The Fair Selling construction uses the MMS le TPS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L327-L340
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L327-L340

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}

theorem FairSelling.MMS_le_TPS (v p : G → ℝ) (hn : 0 < n)
    (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    MMS n v p ≤ TPS n v p := by sorry
