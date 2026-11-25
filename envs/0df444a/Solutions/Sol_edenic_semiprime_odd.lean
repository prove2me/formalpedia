-- Prove2me | solution 1 for edenic_semiprime_odd
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T06:22:42.853624+00:00
-- url     : https://prove2.me/submissions/514ca84c-ef78-4b36-afda-7fdf0eb48e10

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) : Odd n := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  have hne2 : p ≠ 2 := fun h2 => by
    rw [h2] at hp2
    exact absurd hp2 (by decide)
  obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hne2
  subst hk
  refine ⟨2 * k ^ 2 + 4 * k + 1, ?_⟩
  ring
