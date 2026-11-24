-- Prove2me | Theorems.Thm_FairSelling_exists_assignform_ge
-- name    : FairSelling.exists_assignform_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:25.708936+00:00
-- url     : https://prove2.me/theorems/286c65cf-b4a9-4f45-8bcf-373ce971cc86
-- title:
--   Fair Selling: exists assignform ge
-- statement:
--   Any valid outcome can be re-expressed in assignment form (dumping unallocated goods into
--   part `0`) without decreasing its worst-bundle utility.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L142-L183
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L142-L183

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}

theorem FairSelling.exists_assignform_ge (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g)
    (o : Outcome G n) (ho : o.Valid p) :
    ∃ (assign : G → Option (Fin n)) (m : Fin n → ℝ),
      (∀ j, 0 ≤ m j) ∧ (∑ j, m j ≤ procOf p assign) ∧
      minUtil v o ≤ minUtilData v assign m := by sorry
