-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_pool
-- name    : FairSelling.ChargeTPS.CStage.toStage_pool
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:57:20.254401+00:00
-- url     : https://prove2.me/theorems/0b412fe3-3479-4437-883a-aeabaaa3b52c
-- title:
--   CStage: to Stage pool
-- statement:
--   The CStage construction uses the to Stage pool property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L276-L276
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L276-L276

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

theorem FairSelling.ChargeTPS.CStage.toStage_pool (s : CStage G n) : (s.toStage).pool = s.pool := by sorry
