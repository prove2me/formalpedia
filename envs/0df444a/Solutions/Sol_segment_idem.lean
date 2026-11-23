-- Prove2me | solution 1 for segment_idem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:14:53.178363+00:00
-- url     : https://prove2.me/submissions/d2c27cc2-a7c4-49b6-b192-98171ab570b4

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Theorems.Thm_strict_mono_infinite
import Theorems.Thm_nth_of_strict_mono

set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}
theorem _root_.solution (hm : StrictMono φ) (k : ℕ) :
    Segment φ (φ k) = k := by
  have h_rng : φ k ∈ range φ := by simp
  rw [Segment] ; simp [h_rng, -mem_range]
  rw [nth_of_strict_mono hm]
  have h_eq := Nat.count_nth_of_infinite (p := (· ∈ range φ)) <| strict_mono_infinite hm
  rw [h_eq]
