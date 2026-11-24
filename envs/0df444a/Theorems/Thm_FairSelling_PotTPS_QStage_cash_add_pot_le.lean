-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_cash_add_pot_le
-- name    : FairSelling.PotTPS.QStage.cash_add_pot_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:02:04.270809+00:00
-- url     : https://prove2.me/theorems/2620a642-bbdc-495c-ad30-76ecbc97c2a0
-- title:
--   QStage: cash add pot le
-- statement:
--   The QStage construction uses the cash add pot le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L274-L276
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L274-L276

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

theorem FairSelling.PotTPS.QStage.cash_add_pot_le {s : QStage G n} (hs : s.Good v p eps) {i : Fin n} {g : G}
    (hg : g ∈ s.src i) : s.cash i + s.pot p g ≤ p g := by sorry
