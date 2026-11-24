-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_cost_eq_zero_of_notMem
-- name    : FairSelling.ChargeTPS.cost_eq_zero_of_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:31:31.838842+00:00
-- url     : https://prove2.me/theorems/f9a45dce-5960-45a6-8f53-6371dc08cdda
-- title:
--   Charge TPS: cost eq zero of not Mem
-- statement:
--   The cost of an unserved agent's package is zero.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L164-L167
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L164-L167

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxCharge
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open CStage

theorem FairSelling.ChargeTPS.cost_eq_zero_of_notMem (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) {s : CStage G n}
    (hs : s.Good v p eps) {i : Fin n} (hi : i ∉ s.served) (j : Fin n) : s.cost v p i j = 0 := by sorry
