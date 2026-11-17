-- Prove2me | Theorems.Thm_BranchEscapeRepair_ratio_tsum_tendsto_zero
-- name    : BranchEscapeRepair.ratio_tsum_tendsto_zero
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T15:30:55.205621+00:00
-- url     : https://prove2.me/theorems/4ae8187e-90f3-4a9b-bfff-492ecf62836c
-- title:
--   Vanishing of a countable power-ratio sum under sublinear scaling
-- statement:
--   Let $(d_i)_{i\in I}$ be positive reals with $\sum_i d_i^{-2}<\infty$. Let $X_n>0$ and $X_n/n\to0$. Then
--   $$\lim_{n\to\infty}\sum_{i\in I}\left(\frac{X_n}{X_n+d_i}\right)^n=0.$$
--   This controls an entire summable family under sublinear scaling, without requiring a uniform exponential rate.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandão Bueno. Repair of the large-lambda escape in Section 3 of On the Infinitude of Off-Critical Zeros. Elementary dominated-convergence theorem, no novelty claim.

import Mathlib

theorem BranchEscapeRepair.ratio_tsum_tendsto_zero {ι : Type*} (d : ι → ℝ) (hd : ∀ i, 0 < d i) (hs : Summable (fun i => 1/(d i)^2)) (X : ℕ → ℝ) (hx : ∀ n, 0 < X n) (hlim : Filter.Tendsto (fun n => X n/(n : ℝ)) Filter.atTop (nhds 0)) : Filter.Tendsto (fun n => ∑' i, (X n/(X n+d i))^n) Filter.atTop (nhds 0) := by sorry
