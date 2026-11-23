-- Prove2me | solution 1 for epsilon_ConcatFin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:19:45.151811+00:00
-- url     : https://prove2.me/submissions/76f73bc1-4333-4a82-8cbc-c4540e1a13da

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic

set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}
theorem _root_.solution {L : Set (List A)} :
    {[]} * L = L := by
  ext al ; constructor
  · rintro ⟨al1, al2, h_al1, h_al2, h_al⟩
    simp at h_al1 ; simp [h_al1] at h_al ; simpa [← h_al]
  · intro h_al ; use [], al ; simp [h_al]
