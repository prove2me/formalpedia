-- Prove2me | Theorems.Thm_FairSelling_exists_full_of_valid
-- name    : FairSelling.exists_full_of_valid
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:15:05.89724+00:00
-- url     : https://prove2.me/theorems/455d1dc3-38e4-45a4-b883-0a8d8c3ad9a4
-- title:
--   Fair Selling: exists full of valid
-- statement:
--   **Completion of a valid outcome.**  Given a valid outcome, handing the unallocated goods and
--   the undistributed proceeds to the first agent yields a full allocation (every good sold or
--   allocated, and the proceeds distributed exactly) in which nobody's utility has decreased.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsFull.lean#L30-L123
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsFull.lean#L30-L123

import Mathlib
import Definitions.Def_RequestProject_TwoThirds
import Definitions.Def_RequestProject_LemmaTen
import Definitions.Def_RequestProject_TwoThirdsFull
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.exists_full_of_valid (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (o : Outcome G n) (ho : o.Valid p) :
    ∃ o' : Outcome G n, o'.Full p Finset.univ ∧ o'.sold = o.sold ∧
      ∀ i, util (v i) o i ≤ util (v i) o' i := by sorry
