-- Prove2me | Theorems.Thm_FairSelling_PotTPS_slice_cost_le
-- name    : FairSelling.PotTPS.slice_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:42:15.503868+00:00
-- url     : https://prove2.me/theorems/6ccf56e6-e3cc-47ee-8460-38a84a486eba
-- title:
--   Pot TPS: slice cost le
-- statement:
--   **A slice of a sold good is affordable.**  An agent whose whole package is a slice `a` of the
--   proceeds of the sold good `g`, and which is charged both with the sale loss of `g` and with the
--   capped deduction `min(c, τ)` for the part `c` of the proceeds nobody holds, costs an unserved
--   agent at most `2τ` — whatever the price of `g`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L66-L75
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L66-L75

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]

theorem FairSelling.PotTPS.slice_cost_le (w p : G → ℝ) (t τ : ℝ) (g : G) (a c : ℝ)
    (hac : a + c ≤ p g) (hat : a ≤ τ) (ht : t ≤ 2 * τ) :
    a + (saleLoss w p t g + min c τ) ≤ 2 * τ := by sorry
