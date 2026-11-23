-- Prove2me | solution 1 for empty_ConcatInf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:33:48.030388+00:00
-- url     : https://prove2.me/submissions/85b29e0e-8550-49bf-ba18-608a653cde3d

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic

set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}
theorem _root_.solution {L : Set (Stream' A)} :
    (∅ : Set (List A)) * L = ∅ := by
  ext as ; simp
  rintro ⟨al, as, h_al, _⟩
  simp at h_al
