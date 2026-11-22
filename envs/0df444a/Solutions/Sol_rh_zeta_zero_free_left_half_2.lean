-- Prove2me | solution 2 for rh_zeta_zero_free_left_half
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:33:32.338876+00:00
-- url     : https://prove2.me/submissions/e9d1c042-1d7e-4f97-97b5-5424382a8af6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line



theorem solution (s : ℂ) (h1 : 0 < s.re) (h2 : s.re < (1 : ℝ) / 2) :
    riemannZeta s ≠ 0 :=
  by
  intro hz
  have h := riemannHypothesis_iff_zeros_in_strip_on_line.mp mathlib_riemannHypothesis s hz h1 (by linarith)
  linarith
