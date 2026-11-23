-- Prove2me | solution 1 for reg_lang_iter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:44:31.836797+00:00
-- url     : https://prove2.me/submissions/07265cc6-1871-4cb6-a901-eb9a837079fc

import Definitions.Def_AutomataTheory_Automata_Sum
import Definitions.Def_AutomataTheory_Automata_Prod
import Definitions.Def_AutomataTheory_Automata_PSet
import Definitions.Def_AutomataTheory_Automata_Concat
import Definitions.Def_AutomataTheory_Automata_Loop
import Definitions.Def_AutomataTheory_Automata_Congr
import Definitions.Def_AutomataTheory_Languages_RegLang
import Theorems.Thm_Automata_acc_lang_loop


set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
open Classical
variable {A : Type}
theorem _root_.solution [Inhabited A] {L : Set (List A)}
    (h : RegLang L) : RegLang L∗ := by
  obtain ⟨M, acc, h_fin, h_l⟩ := h
  use (M.Loop acc), {inl ()}
  constructor
  · exact Finite.instSum
  · simp +instances [h_l, Automata.acc_lang_loop]
