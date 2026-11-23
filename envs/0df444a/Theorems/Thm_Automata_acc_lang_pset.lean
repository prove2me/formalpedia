-- Prove2me | Theorems.Thm_Automata_acc_lang_pset
-- name    : Automata.acc_lang_pset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:29:10.44785+00:00
-- url     : https://prove2.me/theorems/8d9ea6ca-cd86-469b-9590-09447ac12f36
-- title:
--   Automata: acc lang pset
-- statement:
--   The language accepted by `M.Pset` is the same as that accepted by `M`,
--   where the accepting states of `M.Pset` are those that contains at least one
--   accepting state of `M`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/PSet.lean#L94-L109
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/PSet.lean#L94-L109

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_PSet
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
attribute [local instance_reducible] NA.PSet
variable {A : Type} (M : NA A) (acc : Set M.State)

theorem Automata.acc_lang_pset :
    M.PSet.toNA.AcceptedLang (M.PSet_Acc acc) = M.AcceptedLang acc := by sorry
