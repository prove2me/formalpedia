-- Prove2me | Theorems.Thm_Automata_choueka_lang_decomp_lemma
-- name    : Automata.choueka_lang_decomp_lemma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:31:57.426616+00:00
-- url     : https://prove2.me/theorems/30fd6c0e-b68d-4ddc-baff-906db21c6c04
-- title:
--   Automata: choueka lang decomp lemma
-- statement:
--   The following lemmas are used to prove that the Choueka language is regular.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L236-L296
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean#L236-L296

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

theorem Automata.choueka_lang_decomp_lemma {M : DA A} {acc : Set M.State} :
    M.ChouekaLang acc =
    ⋃ s ∈ acc, { al | al ≠ [] ∧ M.RunOn al = s } *
      ( { al | al ≠ [] ∧ M.RunOn al = M.RunFromOn s al } ∩
        ( { al | al ≠ [] ∧ M.RunOn al = M.RunFromOn s al } * {[]}ᶜ )ᶜ ) := by sorry
