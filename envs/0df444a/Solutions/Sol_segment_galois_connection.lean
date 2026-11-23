-- Prove2me | solution 1 for segment_galois_connection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:34:45.789112+00:00
-- url     : https://prove2.me/submissions/a53ef20c-e905-4359-a4eb-bc0d90906848

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Theorems.Thm_segment_upper_bound
import Theorems.Thm_segment_lower_bound

set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}
theorem _root_.solution (hm : StrictMono φ) (h0 : φ 0 = 0) :
    GaloisConnection φ (Segment φ) := by
  intro m k ; constructor
  · intro h
    by_contra! h_con
    have h1 : Segment φ k + 1 ≤ m := by omega
    have := (StrictMono.le_iff_le hm).mpr h1
    have := segment_upper_bound hm h0 k
    omega
  · intro h
    by_contra! h_con
    have := (StrictMono.le_iff_le hm).mpr h
    have := segment_lower_bound hm h0 k
    omega
