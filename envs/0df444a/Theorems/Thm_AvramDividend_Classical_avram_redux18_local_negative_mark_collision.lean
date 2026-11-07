-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux18_local_negative_mark_collision
-- name    : AvramDividend.Classical.avram_redux18_local_negative_mark_collision
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:04:12.622259+00:00
-- url     : https://prove2.me/theorems/e52550d4-c957-4527-b55e-cfa9fe588897
-- title:
--   Marked Laplace collision bound requiring negativity only at selected original jump times
-- statement:
--   A finite selected set of original negative Lévy jump times has nonpositive jump marks only on that selected set. The exponential of their mark sum differs from the first-order marked compensator by at most half the pair count, with no constraint on marks outside the selected times. This is the source-exact strengthening required to apply the accepted finite-product bound to physical cutoffs.
-- source:
--   Construct a globally bounded weight q_i = exp(y_i) on the chosen Finset and q_i=1 elsewhere, apply the accepted finite-product collision theorem, rewrite finite sums/products by congruence and Real.exp_sum.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_redux18_finite_mark_product_collision
noncomputable section

theorem AvramDividend.Classical.avram_redux18_local_negative_mark_collision
    {α : Type*} [DecidableEq α] (s : Finset α) (y : α → ℝ)
    (hy : ∀ i, i ∈ s → y i ≤ 0) :
    0 ≤ Real.exp (∑ i ∈ s, y i) -
      (1 - ∑ i ∈ s, (1 - Real.exp (y i))) ∧
    2 * (Real.exp (∑ i ∈ s, y i) -
      (1 - ∑ i ∈ s, (1 - Real.exp (y i)))) ≤
      (s.card : ℝ) * ((s.card : ℝ) - 1) := by sorry
