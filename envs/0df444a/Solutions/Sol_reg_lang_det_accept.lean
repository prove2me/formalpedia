-- Prove2me | solution 1 for reg_lang_det_accept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:46:52.306795+00:00
-- url     : https://prove2.me/submissions/aeddcbf9-5824-4a9c-9594-17215bf6b372

import Definitions.Def_AutomataTheory_Automata_Sum
import Definitions.Def_AutomataTheory_Automata_Prod
import Definitions.Def_AutomataTheory_Automata_PSet
import Definitions.Def_AutomataTheory_Automata_Concat
import Definitions.Def_AutomataTheory_Automata_Loop
import Definitions.Def_AutomataTheory_Automata_Congr
import Definitions.Def_AutomataTheory_Languages_RegLang
import Theorems.Thm_Automata_acc_lang_pset


set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
open Classical
variable {A : Type}
theorem _root_.solution {L : Set (List A)} (h : RegLang L) :
    ∃ M : Automata.DA A, ∃ acc : Set M.State, Finite M.State ∧ L = M.toNA.AcceptedLang acc := by
  obtain ⟨M, acc, h_fin, rfl⟩ := h
  use M.PSet, (M.PSet_Acc acc) ; constructor
  · exact Set.instFinite
  · symm ; exact Automata.acc_lang_pset M acc
