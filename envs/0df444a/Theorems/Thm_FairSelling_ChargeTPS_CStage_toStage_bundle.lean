-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
-- name    : FairSelling.ChargeTPS.CStage.toStage_bundle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:16:32.4034+00:00
-- url     : https://prove2.me/theorems/c79d797f-ea80-4708-9649-2f6b4a94f334
-- title:
--   CStage: to Stage bundle
-- statement:
--   The CStage construction uses the to Stage bundle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L272-L272
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L272-L272

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

theorem FairSelling.ChargeTPS.CStage.toStage_bundle (s : CStage G n) : (s.toStage).bundle = s.bundle := by sorry

attribute [defeq] FairSelling.ChargeTPS.CStage.toStage_bundle
