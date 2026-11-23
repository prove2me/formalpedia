-- Prove2me | Theorems.Thm_Automata_pair_path_fin_run
-- name    : Automata.pair_path_fin_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:21:04.488433+00:00
-- url     : https://prove2.me/theorems/d5f00c0d-6ec4-42db-8e91-42032aa0394a
-- title:
--   Automata: pair path fin run
-- statement:
--   The Automata construction uses the pair path fin run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L252-L262
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L252-L262

import Definitions.Def_AutomataTheory_Automata_Hist
import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Pair
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] NA.addHist
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
attribute [local instance_reducible] NA.SingleInit

theorem Automata.pair_path_fin_run [Inhabited A] {s s' : M.State} {al : List A} {ss : Stream' M.State} :
    M.PairPath s s' al ss ↔ (M.SingleInit s).FinRun al.length al.padDefault ss ∧ ss al.length = s' := by sorry
