-- Prove2me | solution 1 for reg_lang_concat_e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:44:18.337917+00:00
-- url     : https://prove2.me/submissions/4742a33e-d6af-46b6-8f1b-c383e0d9db1e

import Definitions.Def_AutomataTheory_Automata_Sum
import Definitions.Def_AutomataTheory_Automata_Prod
import Definitions.Def_AutomataTheory_Automata_PSet
import Definitions.Def_AutomataTheory_Automata_Concat
import Definitions.Def_AutomataTheory_Automata_Loop
import Definitions.Def_AutomataTheory_Automata_Congr
import Definitions.Def_AutomataTheory_Languages_RegLang
import Theorems.Thm_Automata_acc_lang_acc_union
import Theorems.Thm_Automata_acc_lang_concat_e
import Theorems.Thm_Automata_acc_lang_concat_ne
import Theorems.Thm_ConcatFin_epsilon
import Theorems.Thm_ConcatFin_union_distrib


set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
open Classical
variable {A : Type}
theorem _root_.solution {L0 L1 : Set (List A)}
    (h0 : RegLang L0) (h1 : RegLang L1) (h_e : [] ∈ L1) : RegLang (L0 * L1) := by
  obtain ⟨M0, acc0, h_fin0, h_l0⟩ := h0
  obtain ⟨M1, acc1, h_fin1, h_l1⟩ := h1
  use (M0.Concat acc0 M1), (inl '' acc0 ∪ inr '' acc1)
  constructor
  · exact Finite.instSum
  · have h_l1' : L1 = (L1 \ {[]}) ∪ {[]} := by
      symm ; apply Set.diff_union_of_subset ; simp +instances [h_e]
    have h_l1'' : [] ∉ L1 \ {[]} := by simp
    rw [← h_l1] at h_l1' h_l1''
    rw [← h_l0, ← h_l1, h_l1', ConcatFin_union_distrib, ConcatFin_epsilon,
        Automata.acc_lang_acc_union, Automata.acc_lang_concat_e, Automata.acc_lang_concat_ne, union_comm]
