-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_ctotal_le_bound
-- name    : FairSelling.ChargeTPS.ctotal_le_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:40:32.619859+00:00
-- url     : https://prove2.me/theorems/609e5f8f-1ae9-496e-8a3a-fc8f86a84405
-- title:
--   Charge TPS: ctotal le bound
-- statement:
--   The Charge TPS construction uses the ctotal le bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L352-L354
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L352-L354

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
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem FairSelling.ChargeTPS.ctotal_le_bound (hn : 0 < n) (heps : 0 ≤ eps) (hp : ∀ g, 0 ≤ p g) {s : CStage G n}
    (hs : s.Good v p eps) : s.total v p ≤ GeneralTPS.totalBound v p := by sorry
