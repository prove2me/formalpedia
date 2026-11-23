-- Prove2me | solution 1 for reg_lang_epsilon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:19:47.483649+00:00
-- url     : https://prove2.me/submissions/2c96d525-25f2-492c-90c9-41672a79ddb2

import Definitions.Def_AutomataTheory_Automata_Sum
import Definitions.Def_AutomataTheory_Automata_Prod
import Definitions.Def_AutomataTheory_Automata_PSet
import Definitions.Def_AutomataTheory_Automata_Concat
import Definitions.Def_AutomataTheory_Automata_Loop
import Definitions.Def_AutomataTheory_Automata_Congr
import Definitions.Def_AutomataTheory_Languages_RegLang
import Theorems.Thm_P2M_Stream__extract_eq_nil_7f26d60de260


set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
open Classical
variable {A : Type}
theorem _root_.solution [Inhabited A] :
    RegLang ({[]} : Set (List A)) := by
  let M := Automata.NA.mk (A := A) Unit {()} (fun _ _ ↦ {})
  use M, {()} ; constructor
  · exact Finite.of_fintype Unit
  ext al ; simp ; constructor
  · rintro ⟨n, as, ⟨ss, ⟨h_init, h_next⟩, h_acc⟩, h_al⟩
    suffices h_n : n = 0 by simp +instances [← h_al, h_n, extract_eq_nil]
    by_contra ; specialize h_next 0 (by omega) ; simp +instances [M] at h_next
  · rintro ⟨rfl⟩
    use 0, (fun k ↦ default) ; simp +instances [extract_eq_nil]
    use (fun k ↦ ()) ; simp +instances [M, Automata.NA.FinRun]
