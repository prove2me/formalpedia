-- Prove2me | Theorems.Thm_Automata_da_fin_run_unique
-- name    : Automata.da_fin_run_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:13:33.62025+00:00
-- url     : https://prove2.me/theorems/abe16f75-718a-422f-a581-fd48633960bc
-- title:
--   Automata: da fin run unique
-- statement:
--   A `DA` has a unique finite run on any finite input.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L81-L90
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L81-L90

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Det
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type}
attribute [local instance_reducible] DA.toNA
variable {M : DA A}

theorem Automata.da_fin_run_unique {n : ℕ} {as : Stream' A} {ss : Stream' M.State}
    (h : M.toNA.FinRun n as ss) : ∀ k < n + 1, ss k = M.DetRun as k := by sorry
