-- Prove2me | solution 1 for reg_lang_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:43:48.499876+00:00
-- url     : https://prove2.me/submissions/d85f714d-702b-4388-a5dd-5e4352d96dfd

import Definitions.Def_AutomataTheory_Automata_Sum
import Definitions.Def_AutomataTheory_Automata_Prod
import Definitions.Def_AutomataTheory_Automata_PSet
import Definitions.Def_AutomataTheory_Automata_Concat
import Definitions.Def_AutomataTheory_Automata_Loop
import Definitions.Def_AutomataTheory_Automata_Congr
import Definitions.Def_AutomataTheory_Languages_RegLang
import Theorems.Thm_P2M_Stream__extract_padDefault_dee05ba3940c


set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
open Classical
variable {A : Type}
theorem _root_.solution [Inhabited A] :
    RegLang (univ : Set (List A)) := by
  let M := Automata.NA.mk (A := A) Unit {()} (fun _ _ ↦ {()})
  use M, {()} ; constructor
  · exact Finite.of_fintype Unit
  ext al ; simp
  use al.length, al.padDefault ; simp +instances [extract_padDefault]
  use (fun _ ↦ ()) ; simp +instances [M, Automata.NA.FinRun]
