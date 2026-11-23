-- Prove2me | Theorems.Thm_Automata_pair_path_split
-- name    : Automata.pair_path_split
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:20:50.295359+00:00
-- url     : https://prove2.me/theorems/7af06381-e127-4851-bfa5-506e420440d2
-- title:
--   Automata: pair path split
-- statement:
--   The Automata construction uses the pair path split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L65-L74
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L65-L74

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

theorem Automata.pair_path_split {s s' : M.State} {al0 al1 : List A} {ss : Stream' M.State}
    (h : M.PairPath s s' (al0 ++ al1) ss) :
    M.PairPath s (ss al0.length) al0 ss ∧ M.PairPath (ss al0.length) s' al1 (ss.drop al0.length) := by sorry
