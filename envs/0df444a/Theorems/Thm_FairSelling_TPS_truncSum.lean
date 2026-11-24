-- Prove2me | Theorems.Thm_FairSelling_TPS_truncSum
-- name    : FairSelling.TPS_truncSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:23:38.487888+00:00
-- url     : https://prove2.me/theorems/445a3789-1d64-4325-9a8f-e07e74e0530f
-- title:
--   Fair Selling: TPS trunc Sum
-- statement:
--   The Fair Selling construction uses the TPS trunc Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L372-L387
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L372-L387

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.TPS_truncSum (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) :
    truncSum n v p (TPS n v p) = TPS n v p := by sorry
