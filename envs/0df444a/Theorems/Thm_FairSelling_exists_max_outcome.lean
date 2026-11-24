-- Prove2me | Theorems.Thm_FairSelling_exists_max_outcome
-- name    : FairSelling.exists_max_outcome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:30:09.969571+00:00
-- url     : https://prove2.me/theorems/3749685e-c0f2-4e0f-850d-8034dd4f6d44
-- title:
--   Fair Selling: exists max outcome
-- statement:
--   There is a valid outcome maximising the worst-bundle utility over all valid outcomes; it can
--   be taken to allocate every good (sold or kept).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L199-L213
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L199-L213

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}

theorem FairSelling.exists_max_outcome (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) (hn : 0 < n) :
    ∃ o : Outcome G n, o.Valid p ∧
      (o.sold ∪ Finset.univ.biUnion o.kept = Finset.univ) ∧
      ∀ o' : Outcome G n, o'.Valid p → minUtil v o' ≤ minUtil v o := by sorry
