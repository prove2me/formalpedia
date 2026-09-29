-- Prove2me | Theorems.Thm_EulerMascheroni_Sondow_integral_bounds
-- name    : EulerMascheroni.Sondow.integral_bounds
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-14T09:54:41.904957+00:00
-- url     : https://prove2.me/theorems/27c6fe99-da87-4ba6-870b-10ab9e038045
-- title:
--   Positive exponential decay of the Sondow integrals
-- statement:
--   For every positive integer $n$,
--   $$0<I_n<16^{-n}.$$
--   This is the integral part of Sondow's Lemma 3. It does not use a bound for the least common multiple or the integral evaluation involving Euler's constant.
-- source:
--   J. Sondow, https://arxiv.org/pdf/math/0209070, v2 (2002). Lemma 3, p. 10. An alternative elementary majorant is proved in the submitted solution.

import Definitions.Def_eulerMascheroni_sondow
open EulerMascheroni.Sondow

theorem EulerMascheroni.Sondow.integral_bounds (n : ℕ) (hn : 0 < n) :
    0 < I n ∧ I n < (1/16:ℝ)^n := by sorry
