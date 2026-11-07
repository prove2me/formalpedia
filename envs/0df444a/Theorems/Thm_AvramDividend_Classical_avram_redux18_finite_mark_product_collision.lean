-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux18_finite_mark_product_collision
-- name    : AvramDividend.Classical.avram_redux18_finite_mark_product_collision
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:24:58.260196+00:00
-- url     : https://prove2.me/theorems/f8c42afc-fb23-482f-8574-8b125db74133
-- title:
--   Finite marked-jump exponential product collision bound
-- statement:
--   For finitely many marked jump factors q_i between zero and one, the product error above the linear approximation 1−∑(1−q_i) is nonnegative and bounded by half the falling factorial of the number of marks. For genuine negative Lévy marks take q_i=exp(y_i). This allows the original marked-jump Laplace functional to be approximated to quadratic order on each short time cell, using the Proved original full-cutoff collision moment bound cd66a508, without first establishing independent Poisson mark bins.
-- source:
--   Prove by Finset induction: E(insert i s)=q_i E(s)+(1−q_i)Σ_s(1−q_j). Nonnegativity follows from 0≤q≤1; the sum is bounded by the cardinality, yielding the pair-count bound by induction. This targets original Laplace child 81b0ea8d via a mathematically different route from the Poisson-count PGF approach.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_redux18_finite_mark_product_collision
    {α : Type*} [DecidableEq α] (s : Finset α) (q : α → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) :
    0 ≤ (∏ i ∈ s, q i) - (1 - ∑ i ∈ s, (1 - q i)) ∧
    2 * ((∏ i ∈ s, q i) - (1 - ∑ i ∈ s, (1 - q i))) ≤
      (s.card : ℝ) * ((s.card : ℝ) - 1) := by sorry
