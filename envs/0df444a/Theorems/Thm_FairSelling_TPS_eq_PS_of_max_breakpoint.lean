-- Prove2me | Theorems.Thm_FairSelling_TPS_eq_PS_of_max_breakpoint
-- name    : FairSelling.TPS_eq_PS_of_max_breakpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:30:57.458796+00:00
-- url     : https://prove2.me/theorems/f3b14cbf-8927-482b-b0bb-999788cf2316
-- title:
--   Fair Selling: TPS eq PS of max breakpoint
-- statement:
--   **The algorithm stops at the largest breakpoint** (`k = 1`): then `TPS = PS`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L354-L357
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L354-L357

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.TPS_eq_PS_of_max_breakpoint (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {a : ℝ}
    (hmax : ∀ s ∈ breakpoints v p, s ≤ a) (hfa : a ≤ truncSum n v p a) :
    TPS n v p = PS n v p := by sorry
