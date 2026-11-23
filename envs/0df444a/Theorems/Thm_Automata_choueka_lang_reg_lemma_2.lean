-- Prove2me | Theorems.Thm_Automata_choueka_lang_reg_lemma_2
-- name    : Automata.choueka_lang_reg_lemma_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:31:48.62246+00:00
-- url     : https://prove2.me/theorems/09292b4c-4dfa-4db7-8672-0f89ff113ef6
-- title:
--   Automata: choueka lang reg lemma 2
-- statement:
--   The Automata construction uses the choueka lang reg lemma 2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L304-L308
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L304-L308

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

theorem Automata.choueka_lang_reg_lemma_2 [Inhabited A] {M : DA A} [Finite M.State] (s t : M.State) :
    RegLang { al | M.RunFromOn s al = t } := by sorry
