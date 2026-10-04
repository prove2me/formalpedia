-- Prove2me | Theorems.Thm_AgrawalGoyalTS_TwoArmed_expected_firstExceed_eq
-- name    : AgrawalGoyalTS.TwoArmed.expected_firstExceed_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:08:03.891742+00:00
-- url     : https://prove2.me/theorems/9478b06f-8a08-4ac7-83b3-641e4cf07e88
-- title:
--   Lemma 1 — expectation of X(j, s, y)
-- statement:
--   For integers $j\ge 0$ and $0\le s\le j$ and a threshold $y\in[0,1]$, let $X(j,s,y)$ be the number of trials before an i.i.d. sequence of $\mathrm{Beta}(s+1,j-s+1)$ random variables first exceeds $y$ (a geometric random variable with success probability $1-F^{beta}_{s+1,j-s+1}(y)$, equal to $+\infty$ if the success probability is $0$). Then
--   $$\mathbb E[X(j,s,y)]=\frac{1}{F^B_{j+1,y}(s)}-1,$$
--   where $F^B_{n,p}$ is the cdf of $\mathrm{Binomial}(n,p)$.
--
--   In the analysis of Thompson Sampling, $X(j,s(j),y)$ dominates the number of rounds the optimal arm waits between its $j$-th and $(j+1)$-th plays, so this lemma turns waiting times into binomial cdfs.
--
--   **Formalization Note** Both sides are taken in $[0,\infty]$ with $1/0=\infty$. At $y=1$ the success probability is $0$, $X=\infty$ almost surely, and $F^B_{j+1,1}(s)=0$ for $s\le j$, so the identity reads $\infty=\infty$, as in the paper.
-- source:
--   Agrawal and Goyal, Analysis of Thompson Sampling for the Multi-armed Bandit Problem, arXiv:1111.1797v3, p. 6, Lemma 1 (with the definition of X(j, s, y) just above it)

import Mathlib
import Definitions.Def_AgrawalGoyalTS_TwoArmed_BetaBinomial

open MeasureTheory

namespace AgrawalGoyalTS.TwoArmed

/-- Lemma 1 (p. 6): for all natural `j`, `s ≤ j` and `y ∈ [0,1]`,
`E[X(j, s, y)] = 1 / F^B_{j+1,y}(s) - 1`, where `X(j, s, y)` is the number of trials before an
i.i.d. `Beta(s+1, j-s+1)` sequence first exceeds `y`. Stated in `ℝ≥0∞`, so that at `y = 1`
both sides are `∞`. -/
theorem expected_firstExceed_eq (j s : ℕ) (hs : s ≤ j) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∫⁻ ω, ENat.toENNReal (firstExceed y ω) ∂(betaTrials s (j - s)) =
      1 / ENNReal.ofReal (binomCDF (j + 1) y (s : ℝ)) - 1 := by sorry

end AgrawalGoyalTS.TwoArmed
