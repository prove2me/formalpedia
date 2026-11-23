-- Prove2me | Theorems.Thm_Automata_na_hist_inf_run_exists
-- name    : Automata.na_hist_inf_run_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:28:00.787346+00:00
-- url     : https://prove2.me/theorems/c3f97abb-e9f1-42b8-bec9-bbf53bc0dfd1
-- title:
--   Automata: na hist inf run exists
-- statement:
--   Any infinite run of the original NA can be extended to an infinite run of
--   the history NA, assuming that the history component can always "follow along".
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Hist.lean#L87-L98
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Hist.lean#L87-L98

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Hist
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A H : Type}
attribute [local instance_reducible] NA.addHist
variable {M : NA A} {hist_init : Set H} {hist_next : M.State × H → A → Set H}

theorem Automata.na_hist_inf_run_exists {as : Stream' A} {ss : Stream' M.State}
    (h_init : hist_init.Nonempty) (h_next : ∀ s a, (hist_next s a).Nonempty)
    (h : M.InfRun as ss) : ∃ hs : Stream' H, (M.addHist hist_init hist_next).InfRun as (fun k ↦ (ss k, hs k)) := by sorry
