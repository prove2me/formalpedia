-- Prove2me | solution 1 for edenic_semiprime_succ_is_square
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T06:22:54.279942+00:00
-- url     : https://prove2.me/submissions/3563366f-ac2b-4f63-b211-2e02ceaa649f

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    ∃ k, n + 1 = k ^ 2 := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  exact ⟨p + 1, by ring⟩
