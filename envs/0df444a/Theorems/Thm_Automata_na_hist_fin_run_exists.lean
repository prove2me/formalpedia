-- Prove2me | Theorems.Thm_Automata_na_hist_fin_run_exists
-- name    : Automata.na_hist_fin_run_exists
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:28:07.055234+00:00
-- url     : https://prove2.me/theorems/610362be-25c7-4f28-ab28-4c3ddca5cc0f
-- title:
--   Automata: na hist fin run exists
-- statement:
--   Any finite run of the original NA can be extended to a finite run of
--   the history NA, assuming that the history component can always "follow along".
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Hist.lean#L71-L82
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Hist.lean#L71-L82

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Hist
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A H : Type}
attribute [local instance_reducible] NA.addHist
variable {M : NA A} {hist_init : Set H} {hist_next : M.State × H → A → Set H}

theorem Automata.na_hist_fin_run_exists {n : ℕ} {as : Stream' A} {ss : Stream' M.State}
    (h_init : hist_init.Nonempty) (h_next : ∀ s a, (hist_next s a).Nonempty)
    (h : M.FinRun n as ss) : ∃ hs : Stream' H, (M.addHist hist_init hist_next).FinRun n as (fun k ↦ (ss k, hs k)) := by sorry
