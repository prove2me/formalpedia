-- Prove2me | solution 1 for infinite_strict_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:32:47.341208+00:00
-- url     : https://prove2.me/submissions/574873ab-0ef2-458f-9259-9b3c93967971

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments

set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}
theorem _root_.solution {ns : Set ℕ} (h : ns.Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ range φ = ns := by
  use Nat.nth (· ∈ ns) ; constructor
  · exact Nat.nth_strictMono h
  · exact Nat.range_nth_of_infinite h
