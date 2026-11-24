-- Prove2me | Theorems.Thm_FairSelling_TPS_lt_of_no_fixed_above
-- name    : FairSelling.TPS_lt_of_no_fixed_above
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:52:30.815179+00:00
-- url     : https://prove2.me/theorems/07f0193d-bc4c-4241-97f7-8d4bb5a3d33a
-- title:
--   Fair Selling: TPS lt of no fixed above
-- statement:
--   **Scanning the breakpoints from the top.**  If `f(b) < b` and `f(s) < s` at every
--   breakpoint `s ≥ b` (breakpoints being the values `v g` and the prices `p g`), then
--   `TPS < b`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L139-L290
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L139-L290

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.TPS_lt_of_no_fixed_above (v p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {b : ℝ}
    (hb : truncSum n v p b < b)
    (hbv : ∀ g, b ≤ v g → truncSum n v p (v g) < v g)
    (hbp : ∀ g, b ≤ p g → truncSum n v p (p g) < p g) :
    TPS n v p < b := by sorry
