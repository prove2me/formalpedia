-- Prove2me | Theorems.Thm_Automata_pair_lang_concat
-- name    : Automata.pair_lang_concat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:30:54.129016+00:00
-- url     : https://prove2.me/theorems/90279168-4d74-4502-b90d-c9620bf46e14
-- title:
--   Automata: pair lang concat
-- statement:
--   The Automata construction uses the pair lang concat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L117-L122
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L117-L122

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

theorem Automata.pair_lang_concat {s s' t: M.State} {al0 al1 : List A}
    (h0 : al0 ∈ M.PairLang s t) (h1 : al1 ∈ M.PairLang t s') : al0 ++ al1 ∈ M.PairLang s s' := by sorry
