-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_bank_nonneg
-- name    : FairSelling.PotTPS.QStage.bank_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:02:09.440407+00:00
-- url     : https://prove2.me/theorems/4a359066-41dd-4995-85dd-8fe96594b23c
-- title:
--   QStage: bank nonneg
-- statement:
--   The QStage construction uses the bank nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L237-L240
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L237-L240

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

theorem FairSelling.PotTPS.QStage.bank_nonneg {s : QStage G n} (hs : s.Good v p eps) : 0 ≤ s.bank := by sorry
