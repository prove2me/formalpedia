-- Prove2me | solution 1 for strict_mono_infinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:11:48.857676+00:00
-- url     : https://prove2.me/submissions/b2acd141-9c43-4c5b-8435-c97b5f4d29ad

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments

set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}
theorem _root_.solution (hm : StrictMono φ) :
    (range φ).Infinite := by
  exact infinite_range_of_injective hm.injective
