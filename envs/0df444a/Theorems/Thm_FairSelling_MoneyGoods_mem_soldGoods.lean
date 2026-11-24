-- Prove2me | Theorems.Thm_FairSelling_MoneyGoods_mem_soldGoods
-- name    : FairSelling.MoneyGoods.mem_soldGoods
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:39:55.678017+00:00
-- url     : https://prove2.me/theorems/63afe0b9-7c08-4cf3-b7cf-d62a59ba5675
-- title:
--   Money Goods: mem sold Goods
-- statement:
--   The Money Goods construction uses the mem sold Goods property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMoney.lean#L79-L81
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMoney.lean#L79-L81

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

theorem FairSelling.MoneyGoods.mem_soldGoods {p : G → ℝ} {g : G} : g ∈ soldGoods p ↔ p g ≠ 0 := by sorry
