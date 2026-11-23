-- Prove2me | Theorems.Thm_Automata_na_hist_inf_run_proj
-- name    : Automata.na_hist_inf_run_proj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:28:03.390815+00:00
-- url     : https://prove2.me/theorems/b5c15f24-f1e5-4449-a232-d74a8905f165
-- title:
--   Automata: na hist inf run proj
-- statement:
--   The original state components of an infinite run of the history NA is
--   an infinite run of the original NA.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Hist.lean#L53-L62
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Hist.lean#L53-L62

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Hist
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A H : Type}
attribute [local instance_reducible] NA.addHist
variable {M : NA A} {hist_init : Set H} {hist_next : M.State × H → A → Set H}

theorem Automata.na_hist_inf_run_proj {as : Stream' A} {ss : Stream' (M.State × H)}
    (h : (M.addHist hist_init hist_next).InfRun as ss) : M.InfRun as (Prod.fst ∘ ss) := by sorry
