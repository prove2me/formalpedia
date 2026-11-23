-- Prove2me | solution 1 for reg_lang_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:44:39.52593+00:00
-- url     : https://prove2.me/submissions/d2abc5c7-7a29-44fb-9d16-4a8410d07acf

import Definitions.Def_AutomataTheory_Automata_Sum
import Definitions.Def_AutomataTheory_Automata_Prod
import Definitions.Def_AutomataTheory_Automata_PSet
import Definitions.Def_AutomataTheory_Automata_Concat
import Definitions.Def_AutomataTheory_Automata_Loop
import Definitions.Def_AutomataTheory_Automata_Congr
import Definitions.Def_AutomataTheory_Languages_RegLang
import Theorems.Thm_Automata_acc_lang_inter


set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
open Classical
variable {A : Type}
theorem _root_.solution [Inhabited A] {L0 L1 : Set (List A)}
    (h0 : RegLang L0) (h1 : RegLang L1) : RegLang (L0 ∩ L1) := by
  obtain ⟨M0, acc0, h_fin0, h_l0⟩ := h0
  obtain ⟨M1, acc1, h_fin1, h_l1⟩ := h1
  let M_u : (i : Fin 2) → Automata.NA A
    | 0 => M0
    | 1 => M1
  let acc_u : (i : Fin 2) → Set (M_u i).State
    | 0 => acc0
    | 1 => acc1
  use (Automata.NA.Prod M_u), (Automata.NA.Prod_Acc M_u acc_u)
  constructor
  · have h_fin : ∀ i, Finite (M_u i).State := by simp +instances [Fin.forall_fin_two, M_u, h_fin0, h_fin1]
    exact Pi.finite
  · ext as
    simp +instances [h_l0, h_l1, Automata.acc_lang_inter M_u acc_u, Fin.forall_fin_two, M_u, acc_u]
