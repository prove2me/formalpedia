-- Prove2me | Theorems.Thm_FairSelling_MoneyGoods_trunc_eq_price_of_mem_soldGoods
-- name    : FairSelling.MoneyGoods.trunc_eq_price_of_mem_soldGoods
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:57:12.31162+00:00
-- url     : https://prove2.me/theorems/e3f84698-a9a5-4d89-a0fe-d67cfa56df5f
-- title:
--   Money Goods: trunc eq price of mem sold Goods
-- statement:
--   In an instance of the class, every good that is sold at the outset is liquid.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMoney.lean#L95-L100
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMoney.lean#L95-L100

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

theorem FairSelling.MoneyGoods.trunc_eq_price_of_mem_soldGoods {v : Fin n → G → ℝ} {p : G → ℝ}
    (hclass : MoneyClass v p) {g : G} (hg : g ∈ soldGoods p) (j : Fin n) :
    trunc (v j) p (TPS n (v j) p) g = p g := by sorry
