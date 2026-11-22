-- Prove2me | solution 3 for riemann_hypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:19:32.662082+00:00
-- url     : https://prove2.me/submissions/c42017e2-19d3-497e-bab7-80399aadf765
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis

theorem solution :
    ∀ s : ℂ, riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) →
      s ≠ 1 →
      s.re = 1 / 2 :=
  fun s hz htriv hone => mathlib_riemannHypothesis s hz htriv hone
