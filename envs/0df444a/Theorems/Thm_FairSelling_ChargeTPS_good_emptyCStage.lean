-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_good_emptyCStage
-- name    : FairSelling.ChargeTPS.good_emptyCStage
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:56:58.036003+00:00
-- url     : https://prove2.me/theorems/7fd2cae2-5b9c-41fb-a77b-fad4b928a3f7
-- title:
--   Charge TPS: good empty CStage
-- statement:
--   The Charge TPS construction uses the good empty CStage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L326-L335
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L326-L335

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

theorem FairSelling.ChargeTPS.good_emptyCStage (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) :
    (emptyCStage G n).Good v p eps := by sorry
