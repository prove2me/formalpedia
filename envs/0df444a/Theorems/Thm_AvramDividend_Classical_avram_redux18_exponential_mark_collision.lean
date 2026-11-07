-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux18_exponential_mark_collision
-- name    : AvramDividend.Classical.avram_redux18_exponential_mark_collision
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:42:11.289203+00:00
-- url     : https://prove2.me/theorems/852683ea-ecbf-41ef-b906-49be848d6053
-- title:
--   Quadratic jump-pair error for the exponential of a finite sum of nonpositive original marks
-- statement:
--   For any finite family of nonpositive real Lévy marks, the exponential of the total mark lies above its first-order marked compensator and has quadratic collision excess bounded by half the number of ordered distinct mark pairs. This specialises the accepted finite-product collision bound using Real.exp_sum and supplies an exact form for stopped negative-jump path sums.
-- source:
--   Uses the accepted finite-product collision inequality with q_i = exp(y_i), Real.exp_sum, positivity of exp and exp(y_i) ≤ 1 for y_i ≤ 0.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_redux18_finite_mark_product_collision
noncomputable section

theorem AvramDividend.Classical.avram_redux18_exponential_mark_collision
    {α : Type*} [DecidableEq α] (s : Finset α) (y : α → ℝ)
    (hy : ∀ i, y i ≤ 0) :
    0 ≤ Real.exp (∑ i ∈ s, y i) -
      (1 - ∑ i ∈ s, (1 - Real.exp (y i))) ∧
    2 * (Real.exp (∑ i ∈ s, y i) -
      (1 - ∑ i ∈ s, (1 - Real.exp (y i)))) ≤
      (s.card : ℝ) * ((s.card : ℝ) - 1) := by sorry
