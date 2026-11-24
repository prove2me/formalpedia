-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_thr_le_TPS
-- name    : FairSelling.ChargeTPS.thr_le_TPS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:27:54.05846+00:00
-- url     : https://prove2.me/theorems/7597e521-fd5c-4c5b-9180-af93d1c84141
-- title:
--   Charge TPS: thr le TPS
-- statement:
--   The threshold is at most the TPS.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxStep.lean#L65-L72
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxStep.lean#L65-L72

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

theorem FairSelling.ChargeTPS.thr_le_TPS (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (j : Fin n) :
    GeneralTPS.thr v p j ≤ TPS n (v j) p := by sorry
