-- Prove2me | solution 1 for frequently_iff_strict_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:12:03.209403+00:00
-- url     : https://prove2.me/submissions/a756a0be-39f4-4cc7-b72d-a04b57ba70f6

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc

set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'
theorem _root_.solution {p : Stream' Prop} :
    (∃ᶠ n in atTop, p n) ↔ ∃ φ : Stream' ℕ, StrictMono φ ∧ ∀ m, p (φ m) := by
  constructor
  · intro h
    exact extraction_of_frequently_atTop h
  · rintro ⟨φ, h_mono, h_p⟩
    apply Nat.frequently_atTop_iff_infinite.mpr
    have h_range : range φ ⊆ {n | p n} := by
      rintro k ⟨m, rfl⟩
      exact h_p m
    apply Infinite.mono h_range
    exact infinite_range_of_injective h_mono.injective
