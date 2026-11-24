-- Prove2me | Theorems.Thm_FairSelling_TPSset_nonempty
-- name    : FairSelling.TPSset_nonempty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:27:50.24983+00:00
-- url     : https://prove2.me/theorems/dab6c8ea-6895-4dd4-86d3-34a7fe0581ec
-- title:
--   Fair Selling: TPSset nonempty
-- statement:
--   The Fair Selling construction uses the TPSset nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L264-L265
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L264-L265

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.TPSset_nonempty (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) :
    (TPSset n v p).Nonempty := by sorry
