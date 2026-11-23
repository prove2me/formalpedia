-- Prove2me | solution 1 for reg_lang_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:47:49.902318+00:00
-- url     : https://prove2.me/submissions/1c2f1bf4-e1fa-47d0-92ad-f75e6a707a5c

import Definitions.Def_AutomataTheory_Automata_Sum
import Definitions.Def_AutomataTheory_Automata_Prod
import Definitions.Def_AutomataTheory_Automata_PSet
import Definitions.Def_AutomataTheory_Automata_Concat
import Definitions.Def_AutomataTheory_Automata_Loop
import Definitions.Def_AutomataTheory_Automata_Congr
import Definitions.Def_AutomataTheory_Languages_RegLang
import Theorems.Thm_reg_lang_det_accept
import Theorems.Thm_Automata_da_acc_lang_compl


set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
open Classical
variable {A : Type}
theorem _root_.solution [Inhabited A] {L : Set (List A)}
    (h : RegLang L) : RegLang Lᶜ := by
  obtain ⟨M, acc, h_fin, h_l⟩ := reg_lang_det_accept h
  use M.toNA, accᶜ ; constructor
  · exact h_fin
  · simp +instances [Automata.da_acc_lang_compl, h_l]
