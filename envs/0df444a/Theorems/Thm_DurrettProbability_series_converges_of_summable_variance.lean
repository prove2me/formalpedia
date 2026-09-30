-- Prove2me | Theorems.Thm_DurrettProbability_series_converges_of_summable_variance
-- name    : DurrettProbability.series_converges_of_summable_variance
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T17:03:13.233766+00:00
-- url     : https://prove2.me/theorems/f930fdfd-674b-470a-a75c-605f841669ba
-- title:
--   Theorem 2.5.6 — summable variances give almost sure convergence
-- statement:
--   Let $X_1,X_2,\dots$ be independent and square-integrable with $\mathbb{E}X_n=0$. If
--   $$\sum_{n=1}^{\infty}\operatorname{var}(X_n)<\infty,$$
--   then with probability one the series $\sum_{n=1}^{\infty}X_n(\omega)$ converges — that is, the
--   partial sums have a real limit for almost every outcome.
--
--   This is the workhorse of the section, and its content is that under independence and centring, a
--   condition on second moments alone is enough: no assumption about the shape of the distributions,
--   no absolute convergence, no monotonicity. Absolute convergence would require
--   $\sum\mathbb{E}|X_n|<\infty$ and is strictly stronger; Durrett's Example 2.5.7 makes the gap
--   concrete with $\mathbb{P}(X_n=\pm n^{-\alpha})=1/2$, where the series converges for $\alpha>1/2$
--   but converges absolutely only for $\alpha>1$.
--
--   The proof runs through Kolmogorov's maximal inequality applied to the increments beyond time $M$:
--   it bounds $\mathbb{P}(\sup_{m\ge M}|S_m-S_M|>\epsilon)$ by
--   $\epsilon^{-2}\sum_{n>M}\operatorname{var}(X_n)$, which tends to zero, so the partial sums are
--   almost surely Cauchy.
--
--   **Formalization Note** Convergence of the series is convergence of the partial sums to a real
--   limit for almost every outcome, following the book's convention, rather than Mathlib's `Summable`,
--   which for real series means absolute convergence and would be a strictly stronger conclusion. The
--   hypothesis `Summable` on the variances is the right reading there, since they are non-negative.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 84 (PDF p. 92), Theorem 2.5.6: 'Suppose X_1, X_2, ... are independent and have EX_n = 0. If sum_{n=1}^{infinity} var(X_n) < infinity then with probability one sum_{n=1}^{infinity} X_n(omega) converges.' The preceding line fixes the convention: 'We say that sum_{n=1}^{infinity} a_n converges if lim_{N -> infinity} sum_{n=1}^{N} a_n exists.' sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_Series

open MeasureTheory ProbabilityTheory Filter

namespace DurrettProbability

theorem series_converges_of_summable_variance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ) (hmean : ∀ i, μ[X i] = 0)
    (hvar : Summable (fun n => Var[X n; μ])) :
    SeriesConvergesAE X μ := by sorry

end DurrettProbability
