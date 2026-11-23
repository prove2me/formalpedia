-- Prove2me | solution 1 for segment_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:22:55.942599+00:00
-- url     : https://prove2.me/submissions/489171e4-1ba8-486f-88f9-9ee4e9018b0b

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Theorems.Thm_nth_of_strict_mono
import Theorems.Thm_count_out_range_pos

set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}
theorem _root_.solution (hm : StrictMono φ) (h0 : φ 0 = 0) (k : ℕ) :
    φ (Segment φ k) ≤ k := by
  rw [nth_of_strict_mono hm (Segment φ k)]
  rcases Classical.em (k ∈ range φ) with h_k | h_k <;> simp [Segment, h_k, -mem_range]
  suffices _ : Nat.nth (· ∈ range φ) (Nat.count (· ∈ range φ) k - 1) < k by omega
  apply Nat.nth_lt_of_lt_count
  have : Nat.count (· ∈ range φ) k > 0 := by exact count_out_range_pos h0 k h_k
  omega
