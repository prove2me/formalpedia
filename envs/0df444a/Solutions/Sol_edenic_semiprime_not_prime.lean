-- Prove2me | solution 1 for edenic_semiprime_not_prime
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T07:29:01.656196+00:00
-- url     : https://prove2.me/submissions/6d51b66e-c7ab-4f51-89e8-27daaae95578

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) : ¬n.Prime := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  have hp3 : 2 ≤ p := hp.two_le
  exact Nat.not_prime_mul hp.ne_one (by omega)
