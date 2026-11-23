-- Prove2me | solution 1 for segment_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:34:09.939347+00:00
-- url     : https://prove2.me/submissions/b767dd22-d579-481f-9e22-92721fc48e7f

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Theorems.Thm_strict_mono_infinite
import Theorems.Thm_nth_of_strict_mono
import Theorems.Thm_segment_plus_one

set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}
theorem _root_.solution (hm : StrictMono φ) (h0 : φ 0 = 0) (k : ℕ) :
    k < φ (Segment φ k + 1) := by
  rw [nth_of_strict_mono hm (Segment φ k + 1), segment_plus_one h0 k]
  suffices _ : k + 1 ≤ Nat.nth (· ∈ range φ) (Nat.count (· ∈ range φ) (k + 1)) by omega
  apply Nat.le_nth_count
  exact strict_mono_infinite hm
