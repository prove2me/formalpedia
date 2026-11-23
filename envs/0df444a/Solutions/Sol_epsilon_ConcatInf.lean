-- Prove2me | solution 1 for epsilon_ConcatInf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:52:58.142724+00:00
-- url     : https://prove2.me/submissions/08063fec-807e-48aa-8f5a-dfae4f3a5d7a

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic

set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}
theorem _root_.solution {L : Set (Stream' A)} :
    ({[]} : Set (List A)) * L = L := by
  ext as ; constructor
  · rintro ⟨al, as, h_al, h_as, rfl⟩ ; simp at h_al
    simp [h_al, h_as, nil_append_stream]
  · intro h_as ; use [], as ; simp [h_as, nil_append_stream]
