-- Prove2me | solution 1 for edenic_semiprime_totient_diff
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T23:37:45.657988+00:00
-- url     : https://prove2.me/submissions/65b6e396-bab3-4040-b561-1ccd25481bc6

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    ∃ p, p.Prime ∧ (p + 2).Prime ∧ n = p * (p + 2) ∧ n - n.totient = 2 * p + 1 := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  refine ⟨p, hp, hp2, rfl, ?_⟩
  have hc : p.Coprime (p + 2) := by
    rw [hp.coprime_iff_not_dvd]
    intro hdvd
    have hdvd2 : p ∣ 2 := (Nat.dvd_add_iff_right (dvd_refl p)).mpr hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · rw [h] at hp
      exact absurd hp Nat.not_prime_one
    · rw [h] at hp2
      exact absurd hp2 (by decide)
  have ht : (p * (p + 2)).totient = (p - 1) * (p + 1) := by
    rw [Nat.totient_mul hc, Nat.totient_prime hp, Nat.totient_prime hp2]
    rw [show (p + 2) - 1 = p + 1 from by omega]
  rw [ht]
  have h2 : 2 ≤ p := hp.two_le
  obtain ⟨s, hs⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
  rw [hs]
  simp only [Nat.add_sub_cancel]
  have h : (s + 1) * (s + 1 + 2) = s * (s + 1 + 1) + (2 * (s + 1) + 1) := by ring
  rw [h]
  exact Nat.add_sub_cancel_left _ _
