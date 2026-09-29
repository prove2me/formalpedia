-- Prove2me | Theorems.Thm_EulerMascheroni_Sondow_integral_identity
-- name    : EulerMascheroni.Sondow.integral_identity
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-14T09:08:21.473856+00:00
-- url     : https://prove2.me/theorems/747d96a7-9576-41e1-801a-228e9d36c4cd
-- title:
--   Sondow integral evaluation
-- statement:
--   For every positive integer $n$,
--   $$I_n=\binom{2n}{n}\gamma+L_n-A_n.$$
--   This is a known analytic identity, left as a formalization obligation.
-- source:
--   Jonathan Sondow, Criteria for Irrationality of Euler's Constant, https://arxiv.org/pdf/math/0209070 (v2, 4 October 2002). Theorem 1, equation (7), pp. 6-9.

import Definitions.Def_eulerMascheroni_sondow
open EulerMascheroni.Sondow

theorem EulerMascheroni.Sondow.integral_identity (n : ℕ) (hn : 0 < n) :
    I n = ((2*n).choose n : ℝ) * Real.eulerMascheroniConstant + L n - (A n : ℝ) := by sorry
