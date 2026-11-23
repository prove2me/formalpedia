-- Prove2me | solution 1 for segment_range_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:25:09.591906+00:00
-- url     : https://prove2.me/submissions/8bd3d810-ea31-4f4b-ba95-5e68c5c90772

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Theorems.Thm_strict_mono_infinite
import Theorems.Thm_nth_of_strict_mono
import Theorems.Thm_segment_idem
import Theorems.Thm_segment_range_gap

set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}
theorem _root_.solution (hm : StrictMono φ) {m k : ℕ}
    (hl : φ m ≤ k) (hu : k < φ (m + 1)) : Segment φ k = m := by
  obtain (rfl | hu') := show φ m = k ∨ φ m < k by omega
  · exact segment_idem hm m
  obtain ⟨j, h_j, rfl⟩ := show ∃ j < φ (m + 1) - φ m - 1, k = j + φ m + 1 by use (k - φ m - 1) ; omega
  induction' j with j h_ind
  · have h1 : φ m ∈ range φ := by use m
    have h2 : φ m + 1 ∉ range φ := by apply segment_range_gap hm (show φ m < φ m + 1 by omega) ; omega
    have h3 := nth_of_strict_mono hm m
    rw [Segment] ; simp [h1, h2, Nat.count_succ, -mem_range] ; rw [h3]
    have h_eq := Nat.count_nth_of_infinite (p := (· ∈ range φ)) <| strict_mono_infinite hm
    rw [h_eq]
  have h_ind' := h_ind (by omega) (by omega) (by omega) (by omega)
  have h1 : j + 1 + φ m ∉ range φ := by apply segment_range_gap hm (show φ m < j + 1 + φ m by omega) ; omega
  have h2 : j + 1 + φ m + 1 ∉ range φ := by apply segment_range_gap hm (show φ m < j + 1 + φ m + 1 by omega) ; omega
  rw [Segment] at h_ind' ⊢
  simp [h1, (show j + φ m + 1 = j + 1 + φ m by omega), -mem_range] at h_ind'
  simp [h1, h2, Nat.count_succ, -mem_range]
  exact h_ind'
