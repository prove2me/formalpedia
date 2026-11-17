-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB30_piecewise_second_derivative
-- name    : AvramDividend.Classical.avram_gbB30_piecewise_second_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T13:39:24.157309+00:00
-- url     : https://prove2.me/theorems/e5bed1b0-b6fc-4499-b48a-500547c6b086
-- title:
--   Positive-reserve source piecewise quadratic second derivative
-- statement:
--   For the exact piecewise source w(z)=0 below zero and 2z-4z² otherwise, certify its second derivative on strictly positive reserves using only local polynomial equality.

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB30_piecewise_second_derivative (y : ℝ) (hy : 0 < y) :
    iteratedDeriv 2 (fun z : ℝ => if z < 0 then 0 else 2 * z - 4 * z ^ 2) y = -8 := by sorry
