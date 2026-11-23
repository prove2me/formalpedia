-- Prove2me | Theorems.Thm_Automata_da_fin_run_exists
-- name    : Automata.da_fin_run_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:13:53.810117+00:00
-- url     : https://prove2.me/theorems/695c27c3-c833-4d22-89b6-3e2ca6ab06ca
-- title:
--   Automata: da fin run exists
-- statement:
--   A `DA` has a finite run on any finite input.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L75-L77
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L75-L77

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

theorem Automata.da_fin_run_exists (n : ℕ) (as : Stream' A) :
    M.toNA.FinRun n as (M.DetRun as) := by sorry
