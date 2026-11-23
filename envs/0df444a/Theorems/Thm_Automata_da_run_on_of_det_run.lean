-- Prove2me | Theorems.Thm_Automata_da_run_on_of_det_run
-- name    : Automata.da_run_on_of_det_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:19:39.544683+00:00
-- url     : https://prove2.me/theorems/4e4d1f73-155d-455d-bb02-cfc570ec5ce3
-- title:
--   Automata: da run on of det run
-- statement:
--   Relatung `DA.RunOn` and `DA.DetRun`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L101-L106
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L101-L106

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

theorem Automata.da_run_on_of_det_run (M : DA A) (as : Stream' A) (n : ℕ) :
    M.RunOn (as.extract 0 n) = M.DetRun as n := by sorry
