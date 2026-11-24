-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_ptotal_le_bound
-- name    : FairSelling.PhaseTPS.ptotal_le_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:36.860421+00:00
-- url     : https://prove2.me/theorems/b5575299-efe5-4bf4-acd3-9cd9ea3b2ad6
-- title:
--   Phase TPS: ptotal le bound
-- statement:
--   The Phase TPS construction uses the ptotal le bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L392-L394
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L392-L394

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem FairSelling.PhaseTPS.ptotal_le_bound (hn : 0 < n) (heps : 0 ≤ eps) (hp : ∀ g, 0 ≤ p g) {s : PStage G n}
    (hs : s.Good v p eps) : s.total v p ≤ GeneralTPS.totalBound v p := by sorry
