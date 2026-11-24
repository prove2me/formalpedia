-- Prove2me | Theorems.Thm_FairSelling_mem_MMSset_iff
-- name    : FairSelling.mem_MMSset_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:30:06.930955+00:00
-- url     : https://prove2.me/theorems/3be11354-6b0b-4de5-ae62-9d321b2e9d7b
-- title:
--   Fair Selling: mem MMSset iff
-- statement:
--   The Fair Selling construction uses the mem MMSset iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L43-L47
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L43-L47

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [Fintype G] [DecidableEq G]

theorem FairSelling.mem_MMSset_iff (hn : 0 < n) (v p : G → ℝ) (r : ℝ) :
    r ∈ MMSset n v p ↔ ∃ o : Outcome G n, o.Valid p ∧ r ≤ minUtil v o := by sorry
