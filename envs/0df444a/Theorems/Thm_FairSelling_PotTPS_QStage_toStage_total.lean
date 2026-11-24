-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_toStage_total
-- name    : FairSelling.PotTPS.QStage.toStage_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:51:31.365449+00:00
-- url     : https://prove2.me/theorems/ccf4f018-d4ef-4067-a6a4-a5bfb633d268
-- title:
--   QStage: to Stage total
-- statement:
--   The QStage construction uses the to Stage total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L480-L480
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L480-L480

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_total

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
variable {v p eps}
omit [Fintype G]

theorem FairSelling.PotTPS.QStage.toStage_total (s : QStage G n) : (s.toStage).total v p = s.total v p := by sorry
