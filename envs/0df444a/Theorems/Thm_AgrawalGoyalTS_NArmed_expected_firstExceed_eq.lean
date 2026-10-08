-- Prove2me | Theorems.Thm_AgrawalGoyalTS_NArmed_expected_firstExceed_eq
-- name    : AgrawalGoyalTS.NArmed.expected_firstExceed_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:25:54.917404+00:00
-- url     : https://prove2.me/theorems/a2ab7278-a630-48fd-96dc-2e18595631f7
-- title:
--   Lemma 1 — expectation of X(j, s, y)
-- statement:
--   Let $j,s$ be non-negative integers with $s\le j$ and let $y\in[0,1]$. Let $X(j,s,y)$ be the number of trials before an independent sequence of $\mathrm{Beta}(s+1,j-s+1)$ random variables first exceeds $y$, and let $F^B_{n,p}$ be the cdf of $\mathrm{Binomial}(n,p)$. Then
--
--   $$\mathbb E\big[X(j,s,y)\big]=\frac{1}{F^B_{j+1,y}(s)}-1 .$$
--
--   The lemma converts the expected waiting time of a geometric variable with a Beta-cdf parameter into a binomial cdf, which is the form in which the waiting times of the first arm enter the regret bound.
--
--   **Formalization Note** Both sides are in $[0,\infty]$. At $y=1$ every trial fails, so $X=\infty$, and $F^B_{j+1,1}(s)=0$ for $s\le j$, so the right side is $1/0-1=\infty$ as well: the degenerate case is the identity $\infty=\infty$, not a junk equation.
-- source:
--   Agrawal and Goyal, Analysis of Thompson Sampling for the Multi-armed Bandit Problem, arXiv:1111.1797v3, p. 6, Lemma 1

import Mathlib
import Definitions.Def_AgrawalGoyalTS_NArmed_BetaBinomial

open MeasureTheory

namespace AgrawalGoyalTS.NArmed

/-- Lemma 1 (p. 6): for all natural `j`, `s ≤ j` and `y ∈ [0,1]`,
`E[X(j, s, y)] = 1 / F^B_{j+1,y}(s) - 1`, where `X(j, s, y)` is the number of trials before an
i.i.d. `Beta(s+1, j-s+1)` sequence first exceeds `y`. Stated in `ℝ≥0∞`, so that at `y = 1`
both sides are `∞`. -/
theorem expected_firstExceed_eq (j s : ℕ) (hs : s ≤ j) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∫⁻ ω, ENat.toENNReal (AgrawalGoyalTS.TwoArmed.firstExceed y ω) ∂(AgrawalGoyalTS.TwoArmed.betaTrials s (j - s)) =
      1 / ENNReal.ofReal (AgrawalGoyalTS.TwoArmed.binomCDF (j + 1) y (s : ℝ)) - 1 := by sorry

end AgrawalGoyalTS.NArmed
