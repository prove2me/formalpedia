-- Prove2me | solution 2 for rh_zeta_zero_free_right_half
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:33:31.562618+00:00
-- url     : https://prove2.me/submissions/53727fc7-a880-4aae-bc1c-1e3fde4c1e00
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line



theorem solution (s : ℂ) (h1 : (1 : ℝ) / 2 < s.re) (h2 : s.re < 1) :
    riemannZeta s ≠ 0 :=
  by
  intro hz
  have h := riemannHypothesis_iff_zeros_in_strip_on_line.mp mathlib_riemannHypothesis s hz (by linarith) h2
  linarith
