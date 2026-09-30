-- Prove2me | Theorems.Thm_ComplementFreeCA_CFRounding_bernoulli_tail
-- name    : ComplementFreeCA.CFRounding.bernoulli_tail
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:16:45.197652+00:00
-- url     : https://prove2.me/theorems/0df73f26-4977-475d-83be-71d27b0d6f16
-- title:
--   Lemma 3.1 — Bernoulli tail: Pr[X > 3 log m / log log m] ≤ 1/m²
-- statement:
--   There is $m_0$ such that the following holds for every $m\ge m_0$. Let $X_1,\dots,X_N$ be any finite number of independent Bernoulli random variables (each takes only the values $0$ and $1$) on a probability space, with $p_i=\Pr[X_i=1]$ and $\sum_i p_i\le 1$. Let $X=X_1+\dots+X_N$. Then
--   $$\Pr\Big[X>\frac{3\log m}{\log\log m}\Big]\le\frac1{m^2}.$$
--
--   This tail bound controls how often a single item is claimed in the randomized-rounding preallocation: the number of bundles containing a fixed item is such a sum with expectation at most $1$.
--
--   **Formalization Note** The printed lemma mixes $n$ and $m$ ("$X_1,\dots,X_n$ (for sufficiently large $n$) … for $1\le i\le m$ … $X=X_1+\dots+X_m$"). The statement here is the reading its application in §3.1.1 requires and that is true: the number $N$ of variables is arbitrary, "sufficiently large" refers to $m$ (the existential $m_0$), and the hypothesis $\sum_i p_i=1$ is relaxed to $\sum_i p_i\le 1$, which is what $E[Z_j]\le1$ provides; the case $\sum_i p_i=1$ is included. $\log$ is the natural logarithm (the paper does not fix a base). Variables are real-valued, measurable, and independent in the sense of Mathlib's `iIndepFun`.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 6, Lemma 3.1

import Mathlib

namespace ComplementFreeCA.CFRounding

open MeasureTheory ProbabilityTheory

universe u

theorem bernoulli_tail :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ (N : ℕ) (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Fin N → Ω → ℝ),
        (∀ i, Measurable (X i)) → iIndepFun X μ →
        (∀ i ω, X i ω = 0 ∨ X i ω = 1) →
        ∑ i, μ.real {ω | X i ω = 1} ≤ 1 →
        μ.real {ω | 3 * Real.log m / Real.log (Real.log m) < ∑ i, X i ω} ≤ 1 / (m : ℝ) ^ 2 := by sorry

end ComplementFreeCA.CFRounding
