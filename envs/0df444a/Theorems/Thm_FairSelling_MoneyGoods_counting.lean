-- Prove2me | Theorems.Thm_FairSelling_MoneyGoods_counting
-- name    : FairSelling.MoneyGoods.counting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:42:50.879701+00:00
-- url     : https://prove2.me/theorems/7999a992-4eb0-4f2e-899e-1119b6a66711
-- title:
--   Money Goods: counting
-- statement:
--   The Money Goods construction uses the counting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMoney.lean#L214-L271
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMoney.lean#L214-L271

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

theorem FairSelling.MoneyGoods.counting (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (hclass : MoneyClass v p)
    {s : Stage G n} (hs : GoodM v p eps s) {j : Fin n} (hj : j ∉ s.served) :
    (2 * ((n : ℝ) - s.served.card) - 1) * thr v p j
      ≤ truncBundle (v j) p (TPS n (v j) p) s.pool + s.bank := by sorry
