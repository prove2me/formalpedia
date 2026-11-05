-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_compact_interior_Lipschitz_of_continuous_derivative
-- name    : AvramDividend.Classical.avram_p3_e_compensator_compact_interior_Lipschitz_of_continuous_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:00:53.782947+00:00
-- url     : https://prove2.me/theorems/b15ca26f-24b8-4f27-b1df-65fccc168f85
-- title:
--   Local C1 compact value-function regularity supplies a bounded Lipschitz constant for original BV jumps
-- statement:
--   If the original BV value function w is differentiable throughout the compact interior interval [a/2,b] and its derivative is continuous there, then there exists an actual nonnegative Lipschitz constant L on that interval. The result is tailored to eliminate the separate local Lipschitz-premise witness from the source-exact stopped nonlinear jump compensator when the value-function C1 regularity is available.
-- source:
--   Extreme-value theorem for abs ∘ deriv w on compact Icc, followed by Mathlib Convex.norm_image_sub_le_of_norm_deriv_le. No clock/admissibility assumptions, no process replacement, no canonical theorem edit.

import Mathlib
open Set
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_compact_interior_Lipschitz_of_continuous_derivative
(w : ℝ → ℝ) (a b : ℝ) (hab : a / 2 ≤ b)
(hdiff : ∀ y ∈ Set.Icc (a / 2) b, DifferentiableAt ℝ w y)
(hcontDeriv : ContinuousOn (deriv w) (Set.Icc (a / 2) b)) :
∃ L : ℝ, 0 ≤ L ∧
  ∀ u ∈ Set.Icc (a / 2) b, ∀ v ∈ Set.Icc (a / 2) b,
    |w u - w v| ≤ L * |u - v| := by sorry
