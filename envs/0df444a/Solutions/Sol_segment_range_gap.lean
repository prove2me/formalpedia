-- Prove2me | solution 1 for segment_range_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:22:56.397154+00:00
-- url     : https://prove2.me/submissions/954e98a4-c1de-498a-b2db-7311b561d2e3

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Theorems.Thm_strict_mono_infinite
import Theorems.Thm_nth_succ_gap
import Theorems.Thm_nth_of_strict_mono

set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}
theorem _root_.solution (hm : StrictMono φ) {m k : ℕ}
    (hl : φ m < k) (hu : k < φ (m + 1)) : k ∉ range φ := by
  rw [nth_of_strict_mono hm m] at hl
  rw [nth_of_strict_mono hm (m + 1)] at hu
  have h_inf := strict_mono_infinite hm
  have h_gap := nth_succ_gap (p := (· ∈ range φ)) h_inf m (k - Nat.nth (· ∈ range φ) m) (by omega) (by omega)
  rw [(show k - Nat.nth (· ∈ range φ) m + Nat.nth (· ∈ range φ) m = k by omega)] at h_gap
  exact h_gap
