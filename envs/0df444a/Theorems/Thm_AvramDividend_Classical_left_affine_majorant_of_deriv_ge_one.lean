-- Prove2me | Theorems.Thm_AvramDividend_Classical_left_affine_majorant_of_deriv_ge_one
-- name    : AvramDividend.Classical.left_affine_majorant_of_deriv_ge_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T12:56:04.829603+00:00
-- url     : https://prove2.me/theorems/dc57a9f9-fa13-44b9-bd57-2b6e54334484
-- title:
--   A derivative bounded below by one forces the left affine cap majorant
-- statement:
--   For any real function v continuous on the closed interval [0,a], differentiable on its interior, with ordinary derivative at least one throughout (0,a), the value at each 0≤z≤a lies below the affine continuation from the right endpoint: v(z)≤v(a)+z−a. This follows by applying the pinned monotoneOn_of_deriv_nonneg mean-value theorem to z↦v(z)−z on the closed interval. The result is the missing calculus link between derivative minimality of the dividend barrier value below cstar and the true nonlocal near-barrier jump-integrand inequality.

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith

open Set

theorem AvramDividend.Classical.left_affine_majorant_of_deriv_ge_one (v : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hcont : ContinuousOn v (Icc 0 a))
    (hdiff : ∀ z ∈ Ioo 0 a, DifferentiableAt ℝ v z)
    (hder : ∀ z ∈ Ioo 0 a, 1 ≤ deriv v z) :
    ∀ z : ℝ, 0 ≤ z → z ≤ a → v z ≤ z - a + v a := by sorry
