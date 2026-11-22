-- Prove2me | solution 2 for zeta_ne_zero_of_strip_of_two_lt_abs_im
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:30:28.946113+00:00
-- url     : https://prove2.me/submissions/f167d2a7-d767-4bab-9d2a-65c20b17a7fd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis

open Complex

theorem solution (s : ℂ) (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    (him : 2 < |s.im|) : riemannZeta s ≠ 0 :=
  by
  intro hz
  have htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hone : s ≠ 1 := fun h => by rw [h] at h1; norm_num at h1
  have hhalf := mathlib_riemannHypothesis s hz htriv hone
  linarith
