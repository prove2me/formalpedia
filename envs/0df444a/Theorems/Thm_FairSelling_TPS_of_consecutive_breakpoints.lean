-- Prove2me | Theorems.Thm_FairSelling_TPS_of_consecutive_breakpoints
-- name    : FairSelling.TPS_of_consecutive_breakpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:30:46.237734+00:00
-- url     : https://prove2.me/theorems/65a3eb89-0e0a-4a86-bddd-0bd83f897a75
-- title:
--   Fair Selling: TPS of consecutive breakpoints
-- statement:
--   **The algorithm stops below the largest breakpoint** (`k > 1`): the `TPS` lies in the
--   interval `[a, c)` between the stopping breakpoint `a` and the previous one `c`, and it is the
--   solution `C/(n − k)` of the linear equation satisfied by `f` there.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L363-L375
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L363-L375

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.TPS_of_consecutive_breakpoints (v p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g)
    {a c : ℝ} (hac : a < c) (hc : c ∈ breakpoints v p)
    (hgap : ∀ s ∈ breakpoints v p, s ≤ a ∨ c ≤ s)
    (hfa : a ≤ truncSum n v p a)
    (habove : ∀ s ∈ breakpoints v p, c ≤ s → truncSum n v p s < s) :
    ((slopeGoods v p a c).card : ℝ) < n ∧
      TPS n v p = flatConst v p a c / (n - ((slopeGoods v p a c).card : ℝ)) ∧
      a ≤ TPS n v p ∧ TPS n v p < c := by sorry
