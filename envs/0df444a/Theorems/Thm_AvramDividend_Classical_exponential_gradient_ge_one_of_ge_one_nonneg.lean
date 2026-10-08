-- Prove2me | Theorems.Thm_AvramDividend_Classical_exponential_gradient_ge_one_of_ge_one_nonneg
-- name    : AvramDividend.Classical.exponential_gradient_ge_one_of_ge_one_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:25:01.14834+00:00
-- url     : https://prove2.me/theorems/ebee67cf-322d-42ea-8a01-fb4d0c91b414
-- title:
--   Exponential verification test function has derivative at least one for θ≥1 and x≥0
-- statement:
--   For θ≥1 and x≥0, d/dx e^(θx)=θe^(θx)≥1. This is an explicit example satisfying the marginal-dividend inequality w'≥1 required by the Avram local verification step.
-- source:
--   Pinned Mathlib iteratedDeriv_exp_const_mul and Real.one_le_exp.

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.exponential_gradient_ge_one_of_ge_one_nonneg
    (θ x : ℝ) (hθ : 1 ≤ θ) (hx : 0 ≤ x) :
    1 ≤ deriv (fun y : ℝ => Real.exp (θ * y)) x := by sorry
