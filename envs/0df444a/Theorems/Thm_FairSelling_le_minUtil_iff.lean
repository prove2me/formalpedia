-- Prove2me | Theorems.Thm_FairSelling_le_minUtil_iff
-- name    : FairSelling.le_minUtil_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:55.166126+00:00
-- url     : https://prove2.me/theorems/38f07878-aa2d-4dfe-b5be-0ba2cbc61098
-- title:
--   Fair Selling: le min Util iff
-- statement:
--   The Fair Selling construction uses the le min Util iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L37-L40
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L37-L40

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [Fintype G] [DecidableEq G]

theorem FairSelling.le_minUtil_iff (hn : 0 < n) (v : G → ℝ) (o : Outcome G n) (r : ℝ) :
    r ≤ minUtil v o ↔ ∀ j, r ≤ util v o j := by sorry
