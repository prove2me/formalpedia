-- Prove2me | Theorems.Thm_AvramDividend_Classical_quadratic_exponent_limit_nat_multiples_ws01f
-- name    : AvramDividend.Classical.quadratic_exponent_limit_nat_multiples_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:52:17.441531+00:00
-- url     : https://prove2.me/theorems/9389141b-52a1-41e6-83c6-c32303befb51
-- title:
--   Quadratic exponent asymptotics persist along positive integer multiples
-- statement:
--   For any real function f whose normalised values f(n+1)/(n+1)^2 converge along all positive integers, the same quadratic limit holds along the positive-integer subgrid m(n+1) for every positive integer m. This exact analytic subsequence interface allows the three Gaussian Lévy exponential moments at Laplace parameters n+1,m(n+1),2m(n+1) to use the single canonical quadratic Lévy exponent asymptotic, without claiming uniformity over arbitrary real arguments.
-- source:
--   Elementary cofinality of the positive integer subsequence m(n+1) and Filter.Tendsto.comp; WS1F Gaussian three-MGF route.

import Mathlib

open Filter
open scoped Topology

theorem AvramDividend.Classical.quadratic_exponent_limit_nat_multiples_ws01f
    (f : ℝ → ℝ) (a : ℝ)
    (hf : Tendsto (fun n : ℕ =>
      f ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ 2))
      atTop (nhds a))
    (m : ℕ) (hm : 0 < m) :
    Tendsto (fun n : ℕ =>
      f ((m : ℝ) * ((n : ℝ) + 1)) /
        (((m : ℝ) * ((n : ℝ) + 1)) ^ 2))
      atTop (nhds a) := by sorry
