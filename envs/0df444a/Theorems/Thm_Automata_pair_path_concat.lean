-- Prove2me | Theorems.Thm_Automata_pair_path_concat
-- name    : Automata.pair_path_concat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:18:39.540091+00:00
-- url     : https://prove2.me/theorems/ba830dd2-1826-4cbf-8836-c8f07ac43c39
-- title:
--   Automata: pair path concat
-- statement:
--   The Automata construction uses the pair path concat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L102-L115
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean#L102-L115

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

theorem Automata.pair_path_concat {s s' t: M.State} {al0 al1 : List A} {ss0 ss1 : Stream' M.State}
    (h0 : M.PairPath s t al0 ss0) (h1 : M.PairPath t s' al1 ss1) :
    M.PairPath s s' (al0 ++ al1) (fun k ↦ if k < al0.length + 1 then ss0 k else ss1 (k - al0.length)) := by sorry
