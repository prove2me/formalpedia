-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_interior_cap_cutoff_one_sided_derivatives_favourable_kink
-- name    : AvramDividend.Classical.avram_wave5_05_interior_cap_cutoff_one_sided_derivatives_favourable_kink
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:47:16.443479+00:00
-- url     : https://prove2.me/theorems/77c45309-0198-4d37-9809-6702c726442f
-- title:
--   Strictly interior slope-one cutoffs have exact left and right derivatives and nonpositive finite Tanaka kink coefficient
-- statement:
--   For every differentiability point b of w with w'(b)≥1, the slope-one continuation frozen at b is differentiable from the left within (-∞,b] with derivative w'(b), and from the right within [b,∞) with derivative exactly 1. Its finite one-sided derivative jump 1−w'(b) is nonpositive. In Avram's corrected UBV core, any 0<b<c is such a point by the stated strictly interior C² and gradient assumptions. Thus each strictly interior cap-cutoff approximation has a genuine, favourable finite kink coefficient for any correctly derived piecewise Itô–Meyer formula, while nothing is assumed about w'(c−) or C² at c. The full stochastic local time formula remains separate.
-- source:
--   Cap derivative sign hw_grad only strictly inside corrected core 429e17ca-5528-40b5-b593-7c03973d0706; combined with accepted uniform cutoff bound 5d60cc4f-f8cc-4849-8d17-fd65a1331edb. No milestone/core change.

import Mathlib

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave5_05_interior_cap_cutoff_one_sided_derivatives_favourable_kink
    (w : ℝ → ℝ) (b : ℝ)
    (hw_diff : DifferentiableAt ℝ w b)
    (hSlope : 1 ≤ deriv w b) :
    HasDerivWithinAt
      (fun y : ℝ => if y ≤ b then w y else w b + (y - b))
      (deriv w b) (Iic b) b ∧
    HasDerivWithinAt
      (fun y : ℝ => if y ≤ b then w y else w b + (y - b))
      1 (Ici b) b ∧
    1 - deriv w b ≤ 0 := by sorry
