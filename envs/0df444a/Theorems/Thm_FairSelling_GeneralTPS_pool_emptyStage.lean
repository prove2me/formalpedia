-- Prove2me | Theorems.Thm_FairSelling_GeneralTPS_pool_emptyStage
-- name    : FairSelling.GeneralTPS.pool_emptyStage
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:55:43.042808+00:00
-- url     : https://prove2.me/theorems/d816a4f7-398b-48eb-a789-b470ebc2df92
-- title:
--   General TPS: pool empty Stage
-- statement:
--   The General TPS construction uses the pool empty Stage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean#L201-L203
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean#L201-L203

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.GeneralTPS.pool_emptyStage : (emptyStage G n).pool = Finset.univ := by sorry
