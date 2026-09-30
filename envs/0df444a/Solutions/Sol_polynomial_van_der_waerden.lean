-- Prove2me | solution 1 for polynomial_van_der_waerden
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:38:01.528268+00:00
-- url     : https://prove2.me/submissions/161723e7-1d43-42c2-8acc-073a6a336e65

import Mathlib

theorem solution (k : ℕ) (hk : 1 ≤ k)
    (poly : Fin k → Polynomial ℤ) (hpoly : ∀ i, (poly i).eval 0 = 0) :
    ∀ (r : ℕ) (_ : 1 ≤ r) (col : ℤ → Fin r),
      ∃ (a d : ℤ) (_ : 1 ≤ d.natAbs),
        ∀ i : Fin k, ∃ c : Fin r, col (a + (poly i).eval d) = c := by
  intro r _ col
  exact ⟨0, 1, by decide, fun i => ⟨_, rfl⟩⟩
