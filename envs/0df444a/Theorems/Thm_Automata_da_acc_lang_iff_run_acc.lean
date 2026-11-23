-- Prove2me | Theorems.Thm_Automata_da_acc_lang_iff_run_acc
-- name    : Automata.da_acc_lang_iff_run_acc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:14:21.670569+00:00
-- url     : https://prove2.me/theorems/d7c8c476-71a5-439f-bf17-c4e686680907
-- title:
--   Automata: da acc lang iff run acc
-- statement:
--   A finite word `al` is accepted by `M` if and only if `M` reaches an
--   accepting state after running on `al` starting from the initial state.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L117-L128
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean#L117-L128

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

theorem Automata.da_acc_lang_iff_run_acc [Inhabited A] (M : DA A) (acc : Set M.State) (al : List A) :
    al ∈ M.toNA.AcceptedLang acc ↔ M.RunOn al ∈ acc := by sorry
