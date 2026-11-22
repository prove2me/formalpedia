-- Prove2me | solution 4 for riemannZeta_eq_zero_re
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:19:34.222794+00:00
-- url     : https://prove2.me/submissions/8a1fabda-356e-424a-99d6-47d00cb82084
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis

theorem solution :
    ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2 :=
  fun s hz htriv hone => mathlib_riemannHypothesis s hz htriv hone
