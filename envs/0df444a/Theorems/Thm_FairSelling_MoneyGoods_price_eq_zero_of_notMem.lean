-- Prove2me | Theorems.Thm_FairSelling_MoneyGoods_price_eq_zero_of_notMem
-- name    : FairSelling.MoneyGoods.price_eq_zero_of_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:42:28.515614+00:00
-- url     : https://prove2.me/theorems/e303cfcf-d428-41a8-bc94-f2aa203754fd
-- title:
--   Money Goods: price eq zero of not Mem
-- statement:
--   The Money Goods construction uses the price eq zero of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMoney.lean#L84-L86
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMoney.lean#L84-L86

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

theorem FairSelling.MoneyGoods.price_eq_zero_of_notMem {p : G → ℝ} {g : G} (h : g ∉ soldGoods p) : p g = 0 := by sorry
