-- Prove2me | Theorems.Thm_Automata_pair_acc_lang_concat_1
-- name    : Automata.pair_acc_lang_concat_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:31:07.166927+00:00
-- url     : https://prove2.me/theorems/c3bf47f9-1dbc-4334-9508-23f88b28b169
-- title:
--   Automata: pair acc lang concat 1
-- statement:
--   The Automata construction uses the pair acc lang concat 1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L133-L145
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L133-L145

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

theorem Automata.pair_acc_lang_concat_1 {s s' t: M.State} {al0 al1 : List A}
    (h0 : al0 ∈ M.PairLang s t) (h1 : al1 ∈ M.PairAccLang acc t s') : al0 ++ al1 ∈ M.PairAccLang acc s s' := by sorry
