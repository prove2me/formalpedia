-- Prove2me | Theorems.Thm_Automata_na_hist_fin_run_proj
-- name    : Automata.na_hist_fin_run_proj
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:28:02.471742+00:00
-- url     : https://prove2.me/theorems/83748853-f553-407d-9f59-3e7fcdf5e9b6
-- title:
--   Automata: na hist fin run proj
-- statement:
--   The original state components of a finite run of the history NA is
--   a finite run of the original NA.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Hist.lean#L39-L48
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Hist.lean#L39-L48

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Hist
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A H : Type}
attribute [local instance_reducible] NA.addHist
variable {M : NA A} {hist_init : Set H} {hist_next : M.State × H → A → Set H}

theorem Automata.na_hist_fin_run_proj {n : ℕ} {as : Stream' A} {ss : Stream' (M.State × H)}
    (h : (M.addHist hist_init hist_next).FinRun n as ss) : M.FinRun n as (Prod.fst ∘ ss) := by sorry
