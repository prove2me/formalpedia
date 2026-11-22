-- Prove2me | solution 1 for rh_zeta_zero_free_left_half
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T15:17:16.03206+00:00
-- url     : https://prove2.me/submissions/2a040903-f174-4ab7-9b62-6168ac08c80a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_rh_zeta_zero_free_right_half

theorem solution (s : ℂ) (h1 : 0 < s.re) (h2 : s.re < (1 : ℝ)/2) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hn (n : ℕ) : s ≠ -(n : ℂ) := by
    intro hs
    rw [hs] at h1
    simp at h1
    exact (not_lt_of_ge (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))) h1
  have hs1 : s ≠ 1 := by
    intro hs
    rw [hs] at h2
    norm_num at h2
  apply rh_zeta_zero_free_right_half (1-s)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  rw [riemannZeta_one_sub hn hs1, hz, mul_zero]
