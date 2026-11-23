-- Prove2me | Theorems.Thm_Automata_choueka_lang_regular
-- name    : Automata.choueka_lang_regular
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:32:04.888781+00:00
-- url     : https://prove2.me/theorems/d2bed97c-f7c5-4b6f-8bb8-524f9590ad47
-- title:
--   Automata: choueka lang regular
-- statement:
--   The Choueka language of a finite-state deterministic automaton is regular.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L330-L339
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L330-L339

import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
set_option autoImplicit true
open Function Set Filter Stream'
open scoped Computability
open Classical
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] DA.toNA
variable {A : Type}

theorem Automata.choueka_lang_regular [Inhabited A] {M : DA A} [Finite M.State] {acc : Set M.State} :
    RegLang (M.ChouekaLang acc) := by sorry
