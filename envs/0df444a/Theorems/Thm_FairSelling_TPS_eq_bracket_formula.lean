-- Prove2me | Theorems.Thm_FairSelling_TPS_eq_bracket_formula
-- name    : FairSelling.TPS_eq_bracket_formula
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:38:09.805668+00:00
-- url     : https://prove2.me/theorems/3c9a0539-9dd1-41fd-899e-24a69f573ff7
-- title:
--   Fair Selling: TPS eq bracket formula
-- statement:
--   **Correctness of the computation of the `TPS`.**  Suppose `[a, c]` contains no
--   breakpoint in its interior, `f(a) ≥ a`, `f(c) < c`, and `f(s) < s` at every breakpoint
--   `s ≥ c`.  Then, writing `k` for the number of goods with `v(g) ≥ c` and `p(g) ≤ a` and
--   `C` for the constant contribution of the remaining goods, we have `k < n` and
--   `TPS = C/(n − k)`; moreover `a ≤ TPS < c`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L300-L327
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L300-L327

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.TPS_eq_bracket_formula (v p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {a c : ℝ}
    (hac : a ≤ c) (hnb : NoBreak v p a c)
    (hfa : a ≤ truncSum n v p a) (hfc : truncSum n v p c < c)
    (hbv : ∀ g, c ≤ v g → truncSum n v p (v g) < v g)
    (hbp : ∀ g, c ≤ p g → truncSum n v p (p g) < p g) :
    ((slopeGoods v p a c).card : ℝ) < n ∧
      TPS n v p = flatConst v p a c / (n - ((slopeGoods v p a c).card : ℝ)) ∧
      a ≤ TPS n v p ∧ TPS n v p < c := by sorry
