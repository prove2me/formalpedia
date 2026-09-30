-- Prove2me | Theorems.Thm_DurrettProbability_kolmogorov_maximal_inequality
-- name    : DurrettProbability.kolmogorov_maximal_inequality
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T17:02:37.693129+00:00
-- url     : https://prove2.me/theorems/ae564e59-9222-44f9-9982-2ef5f5a9c187
-- title:
--   Theorem 2.5.5 — Kolmogorov's maximal inequality
-- statement:
--   Let $X_1,\dots,X_n$ be independent, square-integrable, with $\mathbb{E}X_i=0$, and write
--   $S_k=X_1+\cdots+X_k$. Then for every $x>0$,
--   $$\mathbb{P}\Bigl(\max_{1\le k\le n}|S_k|\ge x\Bigr)\;\le\;\frac{\operatorname{var}(S_n)}{x^{2}}.$$
--
--   Compare Chebyshev's inequality, which under the same hypotheses bounds only
--   $\mathbb{P}(|S_n|\ge x)$ by the same quantity. The maximal inequality controls the entire path up
--   to time $n$ at no extra cost, and that is what makes it useful: to show a random series converges
--   one needs the partial sums to be uniformly close to each other over a whole tail, not merely close
--   at one time.
--
--   The mechanism is a first-passage decomposition. Let $A_k$ be the event that $|S_k|\ge x$ while
--   $|S_j|<x$ for every $j<k$; the $A_k$ are disjoint, $S_k\mathbb{1}_{A_k}$ depends only on
--   $X_1,\dots,X_k$, and $S_n-S_k$ depends only on $X_{k+1},\dots,X_n$, so independence kills the cross
--   terms in $\mathbb{E}[S_n^2;A_k]$ and leaves $\mathbb{E}[S_k^2;A_k]\ge x^2\mathbb{P}(A_k)$.
--
--   **Formalization Note** The maximum over $1\le k\le n$ is expressed as the existence of such a $k$
--   with $|S_k|\ge x$, which is the same event and avoids introducing a maximum over an index range
--   that is empty when $n=0$; in that case both sides are the trivial bound $0\le\operatorname{var}(S_0)/x^2$.
--   Square-integrability is membership in $L^2$, which is what makes the variances finite.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 84 (PDF p. 92), Theorem 2.5.5: 'Kolmogorov's maximal inequality. Suppose X_1, ..., X_n are independent with EX_i = 0 and var(X_i) < infinity. If S_n = X_1 + ... + X_n then P( max_{1 <= k <= n} |S_k| >= x ) <= x^{-2} var(S_n).' Remark: 'Under the same hypotheses, Chebyshev's inequality (Theorem 1.6.4) gives only P(|S_n| >= x) <= x^{-2} var(S_n).' sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_Series

open MeasureTheory ProbabilityTheory Filter

namespace DurrettProbability

theorem kolmogorov_maximal_inequality {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ) (hmean : ∀ i, μ[X i] = 0)
    (n : ℕ) (x : ℝ) (hx : 0 < x) :
    (μ {ω | ∃ k ∈ Finset.Icc 1 n, x ≤ |partialSum X k ω|}).toReal
      ≤ Var[partialSum X n; μ] / x ^ 2 := by sorry

end DurrettProbability
