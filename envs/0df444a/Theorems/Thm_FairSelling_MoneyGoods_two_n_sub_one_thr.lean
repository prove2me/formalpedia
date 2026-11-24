-- Prove2me | Theorems.Thm_FairSelling_MoneyGoods_two_n_sub_one_thr
-- name    : FairSelling.MoneyGoods.two_n_sub_one_thr
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:57:02.830406+00:00
-- url     : https://prove2.me/theorems/99ddbf05-218d-48e2-9aed-d1ca3af99067
-- title:
--   Money Goods: two n sub one thr
-- statement:
--   The Money Goods construction uses the two n sub one thr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMoney.lean#L152-L157
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMoney.lean#L152-L157

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

theorem FairSelling.MoneyGoods.two_n_sub_one_thr (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (j : Fin n) :
    (2 * (n : ℝ) - 1) * thr v p j = (n : ℝ) * TPS n (v j) p := by sorry
