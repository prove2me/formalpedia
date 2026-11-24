-- Prove2me | Theorems.Thm_FairSelling_MoneyGoods_safe_cost
-- name    : FairSelling.MoneyGoods.safe_cost
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:57:04.154447+00:00
-- url     : https://prove2.me/theorems/dea8ac98-f3bb-4036-b881-b875d781b1b0
-- title:
--   Money Goods: safe cost
-- statement:
--   **A safe bundle costs an unserved agent at most `2τ`.**  This is the step at which the `ε` of
--   the envy condition is paid for by the slack in the threshold.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMoney.lean#L163-L210
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMoney.lean#L163-L210

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

theorem FairSelling.MoneyGoods.safe_cost (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) {s : Stage G n} (hs : GoodM v p eps s)
    {i : Fin n} (hi : i ∈ s.served) {j : Fin n} (hj : j ∉ s.served) :
    truncBundle (v j) p (TPS n (v j) p) (s.bundle i) + s.cash i ≤ 2 * thr v p j := by sorry
