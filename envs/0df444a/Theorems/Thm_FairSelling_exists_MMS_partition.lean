-- Prove2me | Theorems.Thm_FairSelling_exists_MMS_partition
-- name    : FairSelling.exists_MMS_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:26:56.143249+00:00
-- url     : https://prove2.me/theorems/f10d7deb-9e74-4700-8bc3-b761489db0a1
-- title:
--   Fair Selling: exists MMS partition
-- statement:
--   **An MMS partition that allocates every good.** There is a valid outcome allocating every
--   good (sold or kept), for which every part is worth at least `MMS n v p`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L237-L250
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L237-L250

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}

theorem FairSelling.exists_MMS_partition (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧
      (o.sold ∪ Finset.univ.biUnion o.kept = Finset.univ) ∧ ∀ j, MMS n v p ≤ util v o j := by sorry
