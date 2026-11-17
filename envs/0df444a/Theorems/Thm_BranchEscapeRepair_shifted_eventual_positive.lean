-- Prove2me | Theorems.Thm_BranchEscapeRepair_shifted_eventual_positive
-- name    : BranchEscapeRepair.shifted_eventual_positive
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T15:39:22.94461+00:00
-- url     : https://prove2.me/theorems/bd26e57a-ad1e-45ab-9281-9f54b5dbb70f
-- title:
--   Eventual positivity from a separated anchor and a summable complex pole family
-- statement:
--   Let $c>0$, $a_i\ge2c$, $b_i\in\mathbb R$, and $\sum_i a_i^{-2}<\infty$. Let $x_n>0$ satisfy $x_n/n\to0$, and let $L_n\ge1$. Then for all sufficiently large $n$,
--   $$
--   L_n+\Re\sum_i\left(\frac{x_n+c}{x_n+a_i+\mathrm{i}b_i}\right)^n>0.
--   $$
--   The index set may be finite or infinite. This gives a conditional dominance criterion for a positive reference contribution and a separated complex pole family.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandão Bueno. Analytic repair of the large-lambda escape in the Branch manuscripts. No mathematical novelty claim.

import Mathlib

theorem BranchEscapeRepair.shifted_eventual_positive {ι : Type*} (a b : ι → ℝ) (c : ℝ) (hc : 0 < c) (ha : ∀ i, 2*c ≤ a i) (hs : Summable (fun i => 1/(a i)^2)) (x : ℕ → ℝ) (hx : ∀ n, 0 < x n) (hl : Filter.Tendsto (fun n => x n/(n : ℝ)) Filter.atTop (nhds 0)) (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) : ∀ᶠ n in Filter.atTop, 0 < L n + (∑' i, (((x n+c : ℝ) : ℂ)/((x n+a i : ℝ)+(b i : ℂ)*Complex.I))^n).re := by sorry
