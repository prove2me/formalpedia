-- Prove2me | Theorems.Thm_Automata_pair_acc_lang_split
-- name    : Automata.pair_acc_lang_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:30:59.728217+00:00
-- url     : https://prove2.me/theorems/542be439-8c00-495a-8a50-3e8524efe15d
-- title:
--   Automata: pair acc lang split
-- statement:
--   The Automata construction uses the pair acc lang split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L84-L100
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L84-L100

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

theorem Automata.pair_acc_lang_split {s s' : M.State} {al0 al1 : List A}
    (h : al0 ++ al1 ∈ M.PairAccLang acc s s') :
    ∃ t, (al0 ∈ M.PairAccLang acc s t ∧ al1 ∈ M.PairLang t s') ∨
         (al0 ∈ M.PairLang s t ∧ al1 ∈ M.PairAccLang acc t s') := by sorry
