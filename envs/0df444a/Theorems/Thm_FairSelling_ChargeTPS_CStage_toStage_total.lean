-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_total
-- name    : FairSelling.ChargeTPS.CStage.toStage_total
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:57:10.531469+00:00
-- url     : https://prove2.me/theorems/a0c32816-4ea1-45d5-842d-9631f8997086
-- title:
--   CStage: to Stage total
-- statement:
--   The CStage construction uses the to Stage total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L279-L279
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L279-L279

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
open FairSelling.ChargeTPS.CStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
omit [Fintype G]

theorem FairSelling.ChargeTPS.CStage.toStage_total (s : CStage G n) : (s.toStage).total v p = s.total v p := by sorry
