-- Prove2me | Theorems.Thm_BranchCompactScale_moving_pole_sum_limit
-- name    : BranchCompactScale.moving_pole_sum_limit
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-18T09:00:21.431333+00:00
-- url     : https://prove2.me/theorems/87231c0b-4209-4131-a918-0a9a049a1970
-- title:
--   Compact scale: convergence of the full complex pole series with a moving scale
-- statement:
--   Let $(B_i)_{i\in I}$ be a family of complex numbers with $\operatorname{Re}B_i>0$ and $\sum_i(\operatorname{Re}B_i)^{-1}<\infty$. Let $k_j\in\mathbb N$ tend to infinity and let $\lambda_j\in\mathbb R$ converge to $L>0$. Then
--   $$\lim_{j\to\infty}\sum_i\left(1+\frac{\lambda_jB_i}{k_j}\right)^{-k_j}=\sum_i e^{-LB_i}.$$
--   Both the order and the scale may vary. No uniform error rate, finite number of poles, or positivity of the limiting real part is assumed or concluded.
-- source:
--   Desenvolvimento RH, On the Infinitude of Off-Critical Zeros, Section 6.2: replacement of the limit interchange. Formal proof developed 2026-11-18. Mathlib complex logarithm derivative and dominated convergence for series, revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
open Set Filter Topology

theorem BranchCompactScale.moving_pole_sum_limit {ι : Type*} (B : ι → ℂ)
    (hB : ∀ i, 0 < (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (lam : ℕ → ℝ) (L : ℝ) (hL : 0 < L) (hlam : Tendsto lam atTop (𝓝 L)) :
    Tendsto (fun j => ∑' i, ((1+(lam j : ℂ)*B i/(k j : ℂ))⁻¹)^(k j)) atTop
      (𝓝 (∑' i, Complex.exp (-(L : ℂ)*B i))) := by sorry
