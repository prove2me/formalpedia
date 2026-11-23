-- Prove2me | Theorems.Thm_Automata_da_run_from_on_append
-- name    : Automata.da_run_from_on_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:18:02.489935+00:00
-- url     : https://prove2.me/theorems/33ab8f82-cd1a-454c-a82e-5539f741e8e3
-- title:
--   Automata: da run from on append
-- statement:
--   Running on `al1 ++ al2` starting from `s` is the same as running
--   on `al1` starting from `s` and then running on `al2` from the reached state.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L95-L97
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L95-L97

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

theorem Automata.da_run_from_on_append (M : DA A) (s : M.State) (al1 al2 : List A) :
    M.RunFromOn s (al1 ++ al2) = M.RunFromOn (M.RunFromOn s al1) al2 := by sorry
