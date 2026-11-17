-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB30_quadratic_piecewise_positive_jets
-- name    : AvramDividend.Classical.avram_gbB30_quadratic_piecewise_positive_jets
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T13:30:11.336414+00:00
-- url     : https://prove2.me/theorems/b2c2eced-640d-4bbf-af84-a64e303a1aa8
-- title:
--   Original-source piecewise Gaussian quadratic exact first and second derivatives
-- statement:
--   For positive reserve y the piecewise candidate w(z)=0 for z<0 and 2z-4z² for z>=0 has derivative 2-8y and second iterated derivative -8. The facts are used to instantiate the exact original Gaussian generator on the interior cap band.

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB30_quadratic_piecewise_positive_jets (y : ℝ) (hy : 0 < y) :
    deriv (fun z : ℝ => if z < 0 then 0 else 2 * z - 4 * z ^ 2) y = 2 - 8 * y ∧
      iteratedDeriv 2 (fun z : ℝ => if z < 0 then 0 else 2 * z - 4 * z ^ 2) y = -8 := by sorry
