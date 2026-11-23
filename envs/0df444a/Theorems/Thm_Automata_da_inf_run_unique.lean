-- Prove2me | Theorems.Thm_Automata_da_inf_run_unique
-- name    : Automata.da_inf_run_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:19:24.974775+00:00
-- url     : https://prove2.me/theorems/9fd8304b-c1dc-474c-a9ea-ec8ab3e012c2
-- title:
--   Automata: da inf run unique
-- statement:
--   A `DA` has a unique infinite run on any infinite input.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L67-L71
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L67-L71

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

theorem Automata.da_inf_run_unique {as : Stream' A} {ss : Stream' M.State}
    (h : M.toNA.InfRun as ss) : ss = M.DetRun as := by sorry
