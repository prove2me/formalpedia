-- Prove2me | solution 1 for edenic_semiprime_factors_unique
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T07:29:29.548752+00:00
-- url     : https://prove2.me/submissions/9dc0b241-d647-42a1-a152-7dfdbd680ef9

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    ∃ p, p.Prime ∧ (p + 2).Prime ∧ n = p * (p + 2) ∧
      ∀ q r : ℕ, q.Prime → r.Prime → n = q * r → (q = p ∧ r = p + 2) ∨ (q = p + 2 ∧ r = p) := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  refine ⟨p, hp, hp2, rfl, ?_⟩
  intro q r hq hr hqr
  have hqp : q ∣ p * (p + 2) := by
    rw [hqr]
    exact dvd_mul_right q r
  rcases (Nat.Prime.dvd_mul hq).mp hqp with h | h
  · rcases (Nat.dvd_prime hp).mp h with h1 | h1
    · exact absurd h1 hq.ne_one
    · refine Or.inl ⟨h1, ?_⟩
      rw [h1] at hqr
      exact (Nat.mul_left_cancel hp.pos hqr).symm
  · rcases (Nat.dvd_prime hp2).mp h with h1 | h1
    · exact absurd h1 hq.ne_one
    · refine Or.inr ⟨h1, ?_⟩
      rw [h1] at hqr
      have hkey : (p + 2) * r = (p + 2) * p := hqr.symm.trans (Nat.mul_comm p (p + 2))
      exact Nat.mul_left_cancel (by omega) hkey
