-- Prove2me | Theorems.Thm_FairSelling_MMS_le_TPS_le_PS
-- name    : FairSelling.MMS_le_TPS_le_PS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:25:26.055591+00:00
-- url     : https://prove2.me/theorems/10ed2a84-ee99-429a-82c0-9c29e1ca4796
-- title:
--   Fair Selling: MMS le TPS le PS
-- statement:
--   **Lemma 1** of the manuscript: `MMS ≤ TPS ≤ PS`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L400-L403
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L400-L403

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}

theorem FairSelling.MMS_le_TPS_le_PS (v p : G → ℝ) (hn : 0 < n)
    (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    MMS n v p ≤ TPS n v p ∧ TPS n v p ≤ PS n v p := by sorry
