-- Prove2me | Theorems.Thm_Automata_pair_lang_split
-- name    : Automata.pair_lang_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:30:49.518802+00:00
-- url     : https://prove2.me/theorems/8726a46e-39ef-40f1-8023-6e9b2c27144a
-- title:
--   Automata: pair lang split
-- statement:
--   The Automata construction uses the pair lang split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L76-L82
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L76-L82

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

theorem Automata.pair_lang_split {s s' : M.State} {al0 al1 : List A}
    (h : al0 ++ al1 ∈ M.PairLang s s') : ∃ t, al0 ∈ M.PairLang s t ∧ al1 ∈ M.PairLang t s' := by sorry
