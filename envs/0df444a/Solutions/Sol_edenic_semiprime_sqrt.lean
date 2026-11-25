-- Prove2me | solution 1 for edenic_semiprime_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T07:29:26.048249+00:00
-- url     : https://prove2.me/submissions/456457c8-2776-426b-8740-c915f32a4151

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    ∃ k, n + 1 = k ^ 2 ∧ Nat.sqrt n = k - 1 := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  have hp3 : 2 ≤ p := hp.two_le
  refine ⟨p + 1, ?_, ?_⟩
  · ring
  · have hs : p * (p + 2) + 1 = (p + 1) ^ 2 := by ring
    rw [Nat.add_sub_cancel p 1, Nat.eq_sub_of_add_eq hs]
    have hsq1 : p * p ≤ (p + 1) ^ 2 - 1 := by
      rw [show (p + 1) ^ 2 = p ^ 2 + 2 * p + 1 from by ring, Nat.add_sub_cancel, Nat.pow_two]
      exact Nat.le_add_right _ _
    have hle : p ≤ Nat.sqrt ((p + 1) ^ 2 - 1) := Nat.le_sqrt.mpr hsq1
    have hsq2 : (p + 1) ^ 2 - 1 < (p + 1) * (p + 1) := by
      rw [← Nat.pow_two]
      exact Nat.sub_lt (by positivity) (by decide)
    have hlt : Nat.sqrt ((p + 1) ^ 2 - 1) < p + 1 := Nat.sqrt_lt.mpr hsq2
    omega
