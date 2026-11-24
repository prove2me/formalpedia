-- Prove2me | Theorems.Thm_FairSelling_TPS_eq_PS_of_top
-- name    : FairSelling.TPS_eq_PS_of_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:03.069381+00:00
-- url     : https://prove2.me/theorems/bf0b62e4-4ec7-4632-9644-cd5416229c75
-- title:
--   Fair Selling: TPS eq PS of top
-- statement:
--   **The case `k = 1` of the algorithm.**  If `s` dominates every value `v g` and
--   `f(s) ≥ s`, then `TPS = PS`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L127-L133
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L127-L133

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.TPS_eq_PS_of_top (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {s : ℝ}
    (hs : ∀ g, v g ≤ s) (hfs : s ≤ truncSum n v p s) :
    TPS n v p = PS n v p := by sorry
