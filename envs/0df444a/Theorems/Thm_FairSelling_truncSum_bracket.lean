-- Prove2me | Theorems.Thm_FairSelling_truncSum_bracket
-- name    : FairSelling.truncSum_bracket
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:50.984674+00:00
-- url     : https://prove2.me/theorems/403ec89f-9e88-4841-a35e-a2b46358b5cd
-- title:
--   Fair Selling: trunc Sum bracket
-- statement:
--   **Affinity between breakpoints.**  If no breakpoint lies strictly inside `[a, c]`,
--   then for `t ∈ [a, c]` we have `f(t) = (C + k·t)/n`, where `k` is the number of goods
--   whose value is at least `c` and whose price is at most `a`, and `C` is the constant
--   contribution of the other goods.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L93-L112
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L93-L112

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.truncSum_bracket (v p : G → ℝ) {a c t : ℝ} (hnb : NoBreak v p a c)
    (hat : a ≤ t) (htc : t ≤ c) :
    truncSum n v p t
      = (flatConst v p a c + ((slopeGoods v p a c).card : ℝ) * t) / n := by sorry
