-- Prove2me | solution 1 for edenic_semiprime_isSemiprime
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T06:23:01.114271+00:00
-- url     : https://prove2.me/submissions/114b54e7-2d9d-4597-aeb0-dabf3afe53e0

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    Nat.IsSemiprime n := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  exact hp.mul_isAlmostPrime_two hp2
