-- Prove2me | Theorems.Thm_Automata_da_run_on_to_det_run
-- name    : Automata.da_run_on_to_det_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:25:56.384775+00:00
-- url     : https://prove2.me/theorems/1ddd8106-7754-459e-9294-ac192999928b
-- title:
--   Automata: da run on to det run
-- statement:
--   A technical result for extending a finite run to an infinite run.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L110-L112
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L110-L112

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

theorem Automata.da_run_on_to_det_run [Inhabited A] (M : DA A) (al : List A) :
    M.RunOn al = M.DetRun al.padDefault al.length := by sorry
