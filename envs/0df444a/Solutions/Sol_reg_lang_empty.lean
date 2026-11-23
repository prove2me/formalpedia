-- Prove2me | solution 1 for reg_lang_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:28:48.228375+00:00
-- url     : https://prove2.me/submissions/c738a427-0422-4295-8650-75227c894579

import Definitions.Def_AutomataTheory_Automata_Sum
import Definitions.Def_AutomataTheory_Automata_Prod
import Definitions.Def_AutomataTheory_Automata_PSet
import Definitions.Def_AutomataTheory_Automata_Concat
import Definitions.Def_AutomataTheory_Automata_Loop
import Definitions.Def_AutomataTheory_Automata_Congr
import Definitions.Def_AutomataTheory_Languages_RegLang

set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
open Classical
variable {A : Type}
theorem _root_.solution :
    RegLang (∅ : Set (List A)) := by
  let M := Automata.NA.mk (A := A) Unit ∅ (fun _ _ ↦ ∅)
  use M, ∅ ; constructor
  · exact Finite.of_fintype Unit
  ext al ; simp
  rintro ⟨n, as, ⟨ss, _, h_acc⟩, rfl⟩ ; simp at h_acc
