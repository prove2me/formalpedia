-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB30_piecewise_first_derivative
-- name    : AvramDividend.Classical.avram_gbB30_piecewise_first_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T13:39:25.305308+00:00
-- url     : https://prove2.me/theorems/7f6ed91d-8529-43d1-8320-360f2dab3208
-- title:
--   Positive-reserve source piecewise quadratic first derivative
-- statement:
--   For the exact piecewise source w(z)=0 below zero and 2z-4z² otherwise, certify its first derivative on strictly positive reserves using only local polynomial equality.

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB30_piecewise_first_derivative (y : ℝ) (hy : 0 < y) :
    deriv (fun z : ℝ => if z < 0 then 0 else 2 * z - 4 * z ^ 2) y = 2 - 8 * y := by sorry
