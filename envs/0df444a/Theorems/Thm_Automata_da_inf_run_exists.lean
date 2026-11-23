-- Prove2me | Theorems.Thm_Automata_da_inf_run_exists
-- name    : Automata.da_inf_run_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:14:13.149943+00:00
-- url     : https://prove2.me/theorems/542950ea-1f4e-4f9b-a241-344af947bda8
-- title:
--   Automata: da inf run exists
-- statement:
--   A `DA` has an infinite run on any infinite input.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L61-L63
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L61-L63

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

theorem Automata.da_inf_run_exists (as : Stream' A) :
    M.toNA.InfRun as (M.DetRun as) := by sorry
