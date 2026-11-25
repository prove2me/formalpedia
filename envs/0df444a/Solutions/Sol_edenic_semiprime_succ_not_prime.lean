-- Prove2me | solution 1 for edenic_semiprime_succ_not_prime
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T07:29:05.162095+00:00
-- url     : https://prove2.me/submissions/8f6ff13d-fdbf-436f-b441-4efb46a38451

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    ¬(n + 1).Prime := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  have hp3 : 2 ≤ p := hp.two_le
  have hs : p * (p + 2) + 1 = (p + 1) * (p + 1) := by ring
  rw [hs]
  exact Nat.not_prime_mul (by omega) (by omega)
