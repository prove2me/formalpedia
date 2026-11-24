-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_req_eq_thr
-- name    : FairSelling.PotTPS.QStage.req_eq_thr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:26:46.777958+00:00
-- url     : https://prove2.me/theorems/338c7062-1411-46fd-a87d-589f8c178302
-- title:
--   QStage: req eq thr
-- statement:
--   The QStage construction uses the req eq thr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L260-L262
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L260-L262

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_ChargeTPS_req_eq_thr

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
variable {v p eps}
omit [DecidableEq G]

theorem FairSelling.PotTPS.QStage.req_eq_thr {s : QStage G n} {j : Fin n} (hj : j ∉ s.served) :
    s.req v p eps j = GeneralTPS.thr v p j := by sorry
