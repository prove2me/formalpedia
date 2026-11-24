-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_freeBank_nonneg_of
-- name    : FairSelling.PotTPS.QStage.freeBank_nonneg_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:37.408366+00:00
-- url     : https://prove2.me/theorems/f5fe116e-5b41-40c5-a0e8-87bf813ae437
-- title:
--   QStage: free Bank nonneg of
-- statement:
--   The QStage construction uses the free Bank nonneg of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L242-L245
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L242-L245

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
variable {v p eps}

theorem FairSelling.PotTPS.QStage.freeBank_nonneg_of {s : QStage G n} (hs : s.Good v p eps) : 0 ≤ s.freeBank p := by sorry
