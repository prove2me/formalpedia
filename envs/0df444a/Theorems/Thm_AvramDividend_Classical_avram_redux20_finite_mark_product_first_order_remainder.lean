-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux20_finite_mark_product_first_order_remainder
-- name    : AvramDividend.Classical.avram_redux20_finite_mark_product_first_order_remainder
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:30:56.592602+00:00
-- url     : https://prove2.me/theorems/e4a14a69-49e0-4399-a055-95cfcf06bef5
-- title:
--   Finite nonnegative marked-product linearisation has a factorial count error
-- statement:
--   For any finite original marked jump set and individual exponential weights between zero and one, the exact product differs from its first-order sum by a nonnegative remainder bounded by half the second factorial count. This bridges the compensated first moment of true marks and the existing exact original-jump second factorial moment, giving the quadratic small-cell error needed for a Lévy marked-Laplace limit.
-- source:
--   Elementary finite-set induction. Adjoin weight z: the remainder becomes z times the previous remainder plus (1-z) times the previous nonnegative sum of deficits. The first-order sum of deficits is bounded by the existing number of factors. Induction yields the second factorial count.

import Mathlib
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_redux20_finite_mark_product_first_order_remainder
    {α : Type*} [DecidableEq α] (S : Finset α) (z : α → ℝ)
    (hz : ∀ u ∈ S, 0 ≤ z u ∧ z u ≤ 1) :
    0 ≤ (∏ u ∈ S, z u) - (1 - ∑ u ∈ S, (1 - z u)) ∧
    2 * ((∏ u ∈ S, z u) - (1 - ∑ u ∈ S, (1 - z u))) ≤
      (S.card : ℝ) * ((S.card : ℝ) - 1) := by sorry
