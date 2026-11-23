-- Prove2me | solution 1 for count_out_range_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:21:58.443801+00:00
-- url     : https://prove2.me/submissions/1e2b7f17-90ad-495e-9764-967ba9e22a5e

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments

set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}
theorem _root_.solution (h0 : φ 0 = 0) (n : ℕ) (hn : n ∉ range φ) :
    Nat.count (· ∈ range φ) n > 0 := by
  have h0' : 0 ∈ range φ := by use 0
  have h1 : n ≠ 0 := by rintro ⟨rfl⟩ ; contradiction
  have h2 : 1 ≤ n := by omega
  have h3 := Nat.count_monotone (· ∈ range φ) h2
  simp [Nat.count_succ, h0', -mem_range] at h3 ⊢
  omega
