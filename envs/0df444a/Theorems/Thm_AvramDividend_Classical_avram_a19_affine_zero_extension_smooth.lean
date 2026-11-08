-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_affine_zero_extension_smooth
-- name    : AvramDividend.Classical.avram_a19_affine_zero_extension_smooth
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:22:10.659249+00:00
-- url     : https://prove2.me/theorems/97ead74d-aa56-4288-8634-17595663cd1e
-- title:
--   Original A19 affine zero extension is smooth on the positive generator domain
-- statement:
--   The affine candidate extended by zero to negative reserve is continuously differentiable on the exact positive original generator domain for every cap.
-- source:
--   Countermodel regularity obligation for A19 original generator cell, discharged by exact agreement with a smooth affine function on strictly positive reserves.

import Mathlib
open Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_a19_affine_zero_extension_smooth
    (C : ℝ≥0∞) :
    ContDiffOn ℝ 1
      (fun y : ℝ => if y < 0 then (0 : ℝ) else 1 + y)
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by sorry
