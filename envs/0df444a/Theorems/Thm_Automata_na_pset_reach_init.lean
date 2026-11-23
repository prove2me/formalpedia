-- Prove2me | Theorems.Thm_Automata_na_pset_reach_init
-- name    : Automata.na_pset_reach_init
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:28:57.143807+00:00
-- url     : https://prove2.me/theorems/2db60052-1fd1-41ac-9da8-4c0ed1c6866f
-- title:
--   Automata: na pset reach init
-- statement:
--   The Automata construction uses the na pset reach init property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/PSet.lean#L42-L44
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/PSet.lean#L42-L44

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_PSet
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type}
attribute [local instance_reducible] NA.PSet
variable {M : NA A}

theorem Automata.na_pset_reach_init (as : Stream' A) :
    M.PSet.DetRun as 0 = M.init := by sorry
