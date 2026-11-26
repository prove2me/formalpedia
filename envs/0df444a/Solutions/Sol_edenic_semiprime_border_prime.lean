-- Prove2me | solution 1 for edenic_semiprime_border_prime
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T23:37:43.254286+00:00
-- url     : https://prove2.me/submissions/2c8a8bb3-8fe0-43c1-919e-b0cbec0b9db2

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n q : ℕ) (h : IsEdenicSemiprime n)
    (hq : q.Prime) (hdvd : q ∣ n) :
    n = q * (q + 2) ∨ n = (q - 2) * q := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h1 | h1
  · have hpq : p = q := (Nat.Prime.dvd_iff_eq hp hq.ne_one).mp h1
    refine Or.inl ?_
    rw [hpq]
  · have hq2 : p + 2 = q := (Nat.Prime.dvd_iff_eq hp2 hq.ne_one).mp h1
    have hpq : p = q - 2 := by omega
    refine Or.inr ?_
    rw [hq2, hpq]
