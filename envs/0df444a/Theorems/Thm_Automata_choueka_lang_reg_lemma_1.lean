-- Prove2me | Theorems.Thm_Automata_choueka_lang_reg_lemma_1
-- name    : Automata.choueka_lang_reg_lemma_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:21:10.106369+00:00
-- url     : https://prove2.me/theorems/130cb0f2-a158-47ce-bd7b-becc410e6669
-- title:
--   Automata: choueka lang reg lemma 1
-- statement:
--   The Automata construction uses the choueka lang reg lemma 1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L298-L302
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L298-L302

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

theorem Automata.choueka_lang_reg_lemma_1 [Inhabited A] {M : DA A} [Finite M.State] (s : M.State) :
    RegLang { al | M.RunOn al = s } := by sorry
