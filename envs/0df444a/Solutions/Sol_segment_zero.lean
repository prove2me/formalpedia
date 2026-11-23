-- Prove2me | solution 1 for segment_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:18:38.281212+00:00
-- url     : https://prove2.me/submissions/ef933e41-18c9-4397-a073-76a5a7c34069

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Theorems.Thm_segment_idem

set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}
theorem _root_.solution (hm : StrictMono φ) (h0 : φ 0 = 0) :
    Segment φ 0 = 0 := by
  calc _ = Segment φ (φ 0) := by simp [h0]
       _ = _ := by simp [segment_idem hm]
