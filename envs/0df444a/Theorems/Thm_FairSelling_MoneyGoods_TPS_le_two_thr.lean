-- Prove2me | Theorems.Thm_FairSelling_MoneyGoods_TPS_le_two_thr
-- name    : FairSelling.MoneyGoods.TPS_le_two_thr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:57:04.227127+00:00
-- url     : https://prove2.me/theorems/c39c02a0-fa87-41c6-992b-2919fa3d3ec7
-- title:
--   Money Goods: TPS le two thr
-- statement:
--   The truncated proportional share is at most twice the threshold.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMoney.lean#L139-L149
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMoney.lean#L139-L149

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxMoney
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.MoneyGoods
open GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.MoneyGoods.TPS_le_two_thr (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g)
    (j : Fin n) : TPS n (v j) p ≤ 2 * thr v p j := by sorry
