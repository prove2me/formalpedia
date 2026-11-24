-- Prove2me | Theorems.Thm_FairSelling_mem_TPSset_zero
-- name    : FairSelling.mem_TPSset_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:25:00.08173+00:00
-- url     : https://prove2.me/theorems/f1fad82b-0f24-4ff2-a934-2bc867adac25
-- title:
--   Fair Selling: mem TPSset zero
-- statement:
--   The Fair Selling construction uses the mem TPSset zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L259-L261
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L259-L261

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.mem_TPSset_zero (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) :
    (0 : ℝ) ∈ TPSset n v p := by sorry
