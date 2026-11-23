-- Prove2me | Theorems.Thm_Automata_choueka_lang_reg_lemma_4
-- name    : Automata.choueka_lang_reg_lemma_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:32:09.576076+00:00
-- url     : https://prove2.me/theorems/69cad7a0-8aad-4144-bf77-74f58f037072
-- title:
--   Automata: choueka lang reg lemma 4
-- statement:
--   The Automata construction uses the choueka lang reg lemma 4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L317-L326
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L317-L326

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

theorem Automata.choueka_lang_reg_lemma_4 [Inhabited A] {M : DA A} [Finite M.State] (s : M.State) :
    RegLang { al | al ≠ [] ∧ M.RunOn al = M.RunFromOn s al } := by sorry
