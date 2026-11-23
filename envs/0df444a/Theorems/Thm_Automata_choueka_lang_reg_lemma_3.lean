-- Prove2me | Theorems.Thm_Automata_choueka_lang_reg_lemma_3
-- name    : Automata.choueka_lang_reg_lemma_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:31:57.254698+00:00
-- url     : https://prove2.me/theorems/d782b045-2001-4c2b-b401-c66c5dbff1b1
-- title:
--   Automata: choueka lang reg lemma 3
-- statement:
--   The Automata construction uses the choueka lang reg lemma 3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L310-L315
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L310-L315

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

theorem Automata.choueka_lang_reg_lemma_3 [Inhabited A] {M : DA A} [Finite M.State] (s : M.State) :
    RegLang { al | al ≠ [] ∧ M.RunOn al = s } := by sorry
