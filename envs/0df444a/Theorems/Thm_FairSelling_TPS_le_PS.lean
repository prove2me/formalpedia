-- Prove2me | Theorems.Thm_FairSelling_TPS_le_PS
-- name    : FairSelling.TPS_le_PS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:25:03.40459+00:00
-- url     : https://prove2.me/theorems/86efd029-880d-477f-97b2-5e02b29a25f6
-- title:
--   Fair Selling: TPS le PS
-- statement:
--   The Fair Selling construction uses the TPS le PS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L346-L351
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L346-L351

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.TPS_le_PS (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) :
    TPS n v p ≤ PS n v p := by sorry
