-- Prove2me | Theorems.Thm_EulerMascheroni_Sondow_scaled_integral_bounds
-- name    : EulerMascheroni.Sondow.scaled_integral_bounds
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-09-14T09:08:41.950168+00:00
-- url     : https://prove2.me/theorems/00b4cd42-5f36-4d22-ab0f-2a87c9194496
-- title:
--   Sondow scaled positive remainder bound
-- statement:
--   For every positive integer $n$,
--   $$0<d_{2n}I_n<2^{-n}.$$
--   This follows from the established bounds $d_{2n}<8^n$ and $0<I_n<16^{-n}$. It is a known estimate awaiting formalization.
-- source:
--   Jonathan Sondow, Criteria for Irrationality of Euler's Constant, https://arxiv.org/pdf/math/0209070 (v2, 4 October 2002). Lemma 3, p. 10.

import Definitions.Def_eulerMascheroni_sondow
open EulerMascheroni.Sondow

theorem EulerMascheroni.Sondow.scaled_integral_bounds (n : ℕ) (hn : 0 < n) :
    0 < (d (2*n) : ℝ) * I n ∧ (d (2*n) : ℝ) * I n < (1/2 : ℝ)^n := by sorry
