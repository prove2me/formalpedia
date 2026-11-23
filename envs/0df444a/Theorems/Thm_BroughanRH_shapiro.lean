-- Prove2me | Theorems.Thm_BroughanRH_shapiro
-- name    : BroughanRH.shapiro
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:18:53.1705+00:00
-- url     : https://prove2.me/theorems/898809d7-d9be-46c8-a403-e8b89e19515b
-- title:
--   Shapiro’s harmonic-number inequality
-- statement:
--   Put $\delta(n)=\prod_{j=1}^{n-1}\operatorname{lcm}(1,\ldots,j)$. For every positive integer $n$, the squared difference between $H_{\delta(n)}$ and $n^2/2$ is less than $36n^3$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 10.1. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem shapiro :
    let δ (n : ℕ) : ℕ := ∏ j ∈ Finset.Ico 1 n, (Finset.Icc 1 j).lcm id
    ∀ n : ℕ, 1 ≤ n → ((harmonic (δ n) : ℝ) - (n : ℝ)^2/2)^2 < 36*(n : ℝ)^3 := by sorry

end BroughanRH
