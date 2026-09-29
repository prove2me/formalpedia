-- Prove2me | solution 1 for zeta_symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T06:27:50.258292+00:00
-- url     : https://prove2.me/submissions/e5eb88e8-ed69-493f-9779-1c7cc5bb3a61

import Mathlib
open Complex Finset Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution (s : ℂ) (h1 : 0 < s.re) (h2 : s.re < 1)
    (hs : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0 := by
  have h_ne_nat : ∀ (n : ℕ), s ≠ -↑n := by
    intro n hn
    have h_re : s.re = (-↑n : ℂ).re := by rw [hn]
    simp only [neg_re, Complex.natCast_re] at h_re
    have : (n : ℝ) ≥ 0 := Nat.cast_nonneg n
    linarith
  have h_ne_one : s ≠ 1 := by
    intro hn
    have h_re : s.re = (1 : ℂ).re := by rw [hn]
    simp only [one_re] at h_re
    linarith
  rw [riemannZeta_one_sub h_ne_nat h_ne_one, hs]
  ring
