-- Prove2me | Theorems.Thm_EulerMascheroni_Sondow_scaled_A_integral
-- name    : EulerMascheroni.Sondow.scaled_A_integral
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-14T09:08:44.60669+00:00
-- url     : https://prove2.me/theorems/e968787d-5f26-4338-af7e-74888eaf4d79
-- title:
--   Clearing the denominators of Sondow harmonic sums
-- statement:
--   For every nonnegative integer $n$,
--   $$d_{2n}A_n\in\mathbb Z.$$
--   The endpoint $n=0$ gives zero. This arithmetic fact clears the harmonic denominators in the integral identity.
-- source:
--   Jonathan Sondow, Criteria for Irrationality of Euler's Constant, https://arxiv.org/pdf/math/0209070 (v2, 4 October 2002). Theorem 1, p. 6; denominator observation following equation (11), p. 8.

import Definitions.Def_eulerMascheroni_sondow
open EulerMascheroni.Sondow

theorem EulerMascheroni.Sondow.scaled_A_integral (n : ℕ) :
    ∃ z : ℤ, (d (2*n) : ℝ) * (A n : ℝ) = z := by sorry
