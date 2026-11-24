-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_TPS_le_two_thr
-- name    : FairSelling.ChargeTPS.TPS_le_two_thr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:23:21.276887+00:00
-- url     : https://prove2.me/theorems/81eb4f08-80ef-4a23-8d4e-1495ec46ee9a
-- title:
--   Charge TPS: TPS le two thr
-- statement:
--   The TPS is at most twice the threshold.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxStep.lean#L76-L85
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxStep.lean#L76-L85

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
omit [DecidableEq G]

theorem FairSelling.ChargeTPS.TPS_le_two_thr (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (j : Fin n) :
    TPS n (v j) p ≤ 2 * GeneralTPS.thr v p j := by sorry
