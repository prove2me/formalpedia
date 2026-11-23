-- Prove2me | solution 1 for segment_plus_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:33:22.875077+00:00
-- url     : https://prove2.me/submissions/028c9124-6d97-4608-8731-a7634b2ab2c7

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Theorems.Thm_count_out_range_pos

set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}
theorem _root_.solution (h0 : φ 0 = 0) (k : ℕ) :
    Segment φ k + 1 = Nat.count (· ∈ range φ) (k + 1) := by
  rcases Classical.em (k ∈ range φ) with h_k | h_k <;> simp [Segment, Nat.count_succ, h_k, -mem_range]
  suffices _ : Nat.count (· ∈ range φ) k > 0 by omega
  exact count_out_range_pos h0 k h_k
