-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_exponential_quotient_bounds
-- name    : AvramDividend.Classical.negative_exponential_quotient_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T22:55:49.557634+00:00
-- url     : https://prove2.me/theorems/879f384c-60f8-4ca3-9de8-888a36ed25b2
-- title:
--   Sharp bound for normalised negative-jump exponential residual
-- statement:
--   For every θ>0 and negative real jump y, the residual (1−exp(θy))/θ lies between zero and |y|. This exact bound shows domination by the finite absolute first moment, the key pointwise estimate for the bounded-variation positive-drift branch of a spectrally negative Lévy exponent.
-- source:
--   Pinned Mathlib Real.exp_le_one_iff and Real.add_one_le_exp, with elementary inequalities; completely independent of Prove2Me imported lemmas.

import Mathlib

theorem AvramDividend.Classical.negative_exponential_quotient_bounds
    (θ y : ℝ) (hθ : 0 < θ) (hy : y < 0) :
    0 ≤ (1 - Real.exp (θ * y)) / θ ∧
      (1 - Real.exp (θ * y)) / θ ≤ |y| := by sorry
