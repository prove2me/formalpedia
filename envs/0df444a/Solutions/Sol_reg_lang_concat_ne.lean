-- Prove2me | solution 1 for reg_lang_concat_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:44:16.720475+00:00
-- url     : https://prove2.me/submissions/f5cf4326-8006-4c2f-acc2-031e0080e1b2

import Definitions.Def_AutomataTheory_Automata_Sum
import Definitions.Def_AutomataTheory_Automata_Prod
import Definitions.Def_AutomataTheory_Automata_PSet
import Definitions.Def_AutomataTheory_Automata_Concat
import Definitions.Def_AutomataTheory_Automata_Loop
import Definitions.Def_AutomataTheory_Automata_Congr
import Definitions.Def_AutomataTheory_Languages_RegLang
import Theorems.Thm_Automata_acc_lang_concat_ne


set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
open Classical
variable {A : Type}
theorem _root_.solution {L0 L1 : Set (List A)}
    (h0 : RegLang L0) (h1 : RegLang L1) (h_ne : [] ∉ L1) : RegLang (L0 * L1) := by
  obtain ⟨M0, acc0, h_fin0, h_l0⟩ := h0
  obtain ⟨M1, acc1, h_fin1, h_l1⟩ := h1
  use (M0.Concat acc0 M1), (inr '' acc1)
  constructor
  · exact Finite.instSum
  · have h_l1' : L1 = L1 \ {[]} := by
      ext al ; simp
      intro h1 h2 ; simp +instances [h2] at h1
      contradiction
    rw [← h_l1] at h_l1'
    rw [← h_l0, ← h_l1, h_l1', Automata.acc_lang_concat_ne]
