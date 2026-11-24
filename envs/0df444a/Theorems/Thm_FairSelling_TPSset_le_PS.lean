-- Prove2me | Theorems.Thm_FairSelling_TPSset_le_PS
-- name    : FairSelling.TPSset_le_PS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:30:05.414292+00:00
-- url     : https://prove2.me/theorems/62afe2cf-813f-4b02-800d-eacb29c51c19
-- title:
--   Fair Selling: TPSset le PS
-- statement:
--   The Fair Selling construction uses the TPSset le PS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L271-L273
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L271-L273

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.TPSset_le_PS (v p : G → ℝ) {t : ℝ} (ht : t ∈ TPSset n v p) :
    t ≤ PS n v p := by sorry
