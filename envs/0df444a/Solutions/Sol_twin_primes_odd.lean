-- Prove2me | solution 1 for twin_primes_odd
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T06:23:06.501585+00:00
-- url     : https://prove2.me/submissions/d8e85b97-e0c0-4794-ac10-21fd1f6064e5

import Mathlib

theorem solution (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) : Odd p ∧ Odd (p + 2) := by
  have hne2 : p ≠ 2 := fun h2 => by
    rw [h2] at hp2
    exact absurd hp2 (by decide)
  obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hne2
  refine ⟨⟨k, hk⟩, k + 1, ?_⟩
  omega
