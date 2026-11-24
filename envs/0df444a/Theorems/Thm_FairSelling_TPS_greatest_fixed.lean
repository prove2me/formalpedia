-- Prove2me | Theorems.Thm_FairSelling_TPS_greatest_fixed
-- name    : FairSelling.TPS_greatest_fixed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:27:54.235769+00:00
-- url     : https://prove2.me/theorems/a734946c-1b91-44c5-b64a-84c267bfcaaf
-- title:
--   Fair Selling: TPS greatest fixed
-- statement:
--   The Fair Selling construction uses the TPS greatest fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L393-L397
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L393-L397

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.TPS_greatest_fixed (v p : G → ℝ) {t : ℝ}
    (ht : truncSum n v p t = t) : t ≤ TPS n v p := by sorry
