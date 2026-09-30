-- Prove2me | Theorems.Thm_DurrettProbability_kolmogorov_three_series
-- name    : DurrettProbability.kolmogorov_three_series
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T17:04:53.263516+00:00
-- url     : https://prove2.me/theorems/40eafc6a-1775-4301-a643-79ca2061c46a
-- title:
--   Theorem 2.5.8 — Kolmogorov's three-series theorem
-- statement:
--   Let $X_1,X_2,\dots$ be independent real random variables, fix a truncation level $A>0$, and set
--   $$Y_n = X_n\,\mathbb{1}(|X_n|\le A).$$
--   Then $\sum_{n}X_n$ converges almost surely **if and only if** all three of the following hold:
--
--   1. $\displaystyle\sum_{n}\mathbb{P}(|X_n|>A)<\infty$;
--   2. $\displaystyle\sum_{n}\mathbb{E}Y_n$ converges;
--   3. $\displaystyle\sum_{n}\operatorname{var}(Y_n)<\infty$.
--
--   Three conditions computable from the marginal distributions decide an almost-sure question about
--   the paths, and each does a distinct job. The first says $X_n$ and $Y_n$ differ only finitely often,
--   so by Borel–Cantelli the two series converge or diverge together. The third, with the convergence
--   criterion for series of centred independent summands, makes $\sum(Y_n-\mathbb{E}Y_n)$ converge. The
--   second puts the means back.
--
--   Nothing is assumed about the integrability of $X_n$: the truncated variables are bounded, so their
--   means and variances exist whatever the tails of $X_n$ do. Nor does the conclusion depend on the
--   choice of $A$ — since the left-hand side does not, the three conditions hold for one $A>0$ exactly
--   when they hold for every $A>0$.
--
--   **Formalization Note** "$\sum_n \mathbb{E}Y_n$ converges" is convergence of the partial sums to a
--   real limit, following the book's explicit convention, and is *not* stated as summability: for real
--   series Mathlib's `Summable` means absolute convergence, which would make condition (ii) strictly
--   stronger and the theorem false as an equivalence. Conditions (i) and (iii) are series of
--   non-negative terms, where the two notions coincide, and are stated as summability.
--
--   Almost-sure convergence of $\sum_n X_n$ asserts, for almost every outcome, the existence of a real
--   limit of the partial sums. No integrability of the $X_n$ is assumed anywhere. Both implications are
--   part of the statement; Durrett proves sufficiency here and defers necessity to Example 3.4.12,
--   where it follows from the Lindeberg–Feller central limit theorem.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 85 (PDF p. 93), Theorem 2.5.8: 'Kolmogorov's three-series theorem. Let X_1, X_2, ... be independent. Let A > 0 and let Y_i = X_i 1(|X_i| <= A). In order that sum_{n=1}^{infinity} X_n converges a.s., it is necessary and sufficient that (i) sum_{n=1}^{infinity} P(|X_n| > A) < infinity, (ii) sum_{n=1}^{infinity} E Y_n converges, and (iii) sum_{n=1}^{infinity} var(Y_n) < infinity.' Proof: 'We will prove the necessity in Example 3.4.12 as an application of the central limit theorem.' sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_Series

open MeasureTheory ProbabilityTheory Filter

namespace DurrettProbability

theorem kolmogorov_three_series {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) (A : ℝ) (hA : 0 < A) :
    SeriesConvergesAE X μ ↔
      (Summable (fun n => (μ {ω | A < |X n ω|}).toReal)
        ∧ (∃ L : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, μ[truncate A (X n)]) atTop (nhds L))
        ∧ Summable (fun n => Var[truncate A (X n); μ])) := by sorry

end DurrettProbability
