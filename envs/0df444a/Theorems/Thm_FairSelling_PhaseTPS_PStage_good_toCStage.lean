-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_PStage_good_toCStage
-- name    : FairSelling.PhaseTPS.PStage.good_toCStage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:26:17.792882+00:00
-- url     : https://prove2.me/theorems/cf16f8fa-4b5a-4bdd-93a0-a3329b0b32f9
-- title:
--   PStage: good to CStage
-- statement:
--   **The invariant transfers to the charged bookkeeping**, hence the whole accounting of
--   `ChargeTPS` — in particular the counting invariant of Algorithm 4 — applies.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L287-L331
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L287-L331

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PhaseTPS.PStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem FairSelling.PhaseTPS.PStage.good_toCStage {s : PStage G n} (hs : s.Good v p eps) :
    (s.toCStage).Good v p eps := by sorry
