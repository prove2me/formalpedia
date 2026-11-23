-- Prove2me | solution 1 for nth_of_strict_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:13:34.384381+00:00
-- url     : https://prove2.me/submissions/d06d9746-8a7b-49c2-b9b3-36a7bb61ed6c

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Theorems.Thm_strict_mono_infinite

set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}
theorem _root_.solution (hm : StrictMono φ) (n : ℕ) :
    φ n = Nat.nth (· ∈ range φ) n := by
  rw [← Nat.nth_comp_of_strictMono hm (by simp)]
  · simp
  intro hf ; exfalso
  have : (range φ).Infinite := strict_mono_infinite hm
  exact absurd hf this
