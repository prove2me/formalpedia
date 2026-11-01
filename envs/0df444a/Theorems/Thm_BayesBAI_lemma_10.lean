-- Prove2me | Theorems.Thm_BayesBAI_lemma_10
-- name    : BayesBAI.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:53:06.662227+00:00
-- url     : https://prove2.me/theorems/eef12f74-27c7-4b91-903d-5739c56f0768
-- title:
--   Lemma 10 — Chernoff and Hoeffding bounds for Bernoulli means
-- statement:
--   Let $x_1,\dots,x_n$ ($n\ge1$) be independent Bernoulli random variables with common mean $\mu$, and let $\hat\mu_n=\frac1n\sum_{t=1}^n x_t$. Write $d_{\mathrm{KL}}(p,q)=p\log\frac pq+(1-p)\log\frac{1-p}{1-q}$. Then:
--
--   1. for $\mu\in(0,1)$, $\epsilon>0$ and $\mu+\epsilon<1$,
--   $$
--   \mathbb P[\hat\mu_n-\mu\ge\epsilon]\le e^{-n\,d_{\mathrm{KL}}(\mu+\epsilon,\mu)};
--   $$
--   2. for $\mu\in(0,1)$, $\epsilon>0$ and $\mu-\epsilon>0$,
--   $$
--   \mathbb P[\hat\mu_n-\mu\le-\epsilon]\le e^{-n\,d_{\mathrm{KL}}(\mu-\epsilon,\mu)};
--   $$
--   3. for every $\epsilon\ge0$,
--   $$
--   \mathbb P[|\hat\mu_n-\mu|\ge\epsilon]\le2e^{-2n\epsilon^2}.\tag{11}
--   $$
--
--   The last bound, applied to each arm with the union bound, gives Lemma 2.
--
--   **Formalization Note.** $d_{\mathrm{KL}}$ is the published `klBern`. Variables are measurable and take values in $\{0,1\}$ almost surely.
--
--   Differences from the source:
--   - encoding: Bernoulli random variables with common mean μ → independent (iIndepFun), measurable, a.s. {0,1}-valued, ∫ x_t = μ; reason: the page omits independence, which the proof and the use in Lemma 2 need: these are i.i.d. draws (Reading 9)
--   - encoding: the two KL bounds, with no stated range; n unrestricted → 0 < μ < 1, ε > 0, and μ + ε < 1 (resp. μ − ε > 0); n ≥ 1; reason: d_KL is defined on (0,1)² (p.4), and μ̂_n needs n ≥ 1
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Lemma 10, eq. (11), p.17

import Mathlib
import Definitions.Def_RegretBandits_Stochastic_klBernoulli

open MeasureTheory ProbabilityTheory

namespace BayesBAI

open RegretBandits.Stochastic in
/-- Lemma 10 (Chernoff bound), Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, p.17: for independent
Bernoulli variables `x₁, …, x_n` of common mean `μ`, with `μ̂_n = (1/n) Σ_t x_t`,
`ℙ[μ̂_n - μ ≥ ε] ≤ exp(-n d_KL(μ + ε, μ))`, `ℙ[μ̂_n - μ ≤ -ε] ≤ exp(-n d_KL(μ - ε, μ))`, and (11)
`ℙ[|μ̂_n - μ| ≥ ε] ≤ 2 exp(-2 n ε²)`.

**Formalization Note.** The page omits independence, which the proof of Lemma 2 needs; it is
`iIndepFun`. `d_KL` is defined on `(0, 1)²` (p.4), which fixes the ranges of `μ` and `ε` in the first two
clauses: `klBern` is the public formula `p log(p/q) + (1-p) log((1-p)/(1-q))`. The third clause is for
all `μ` and `ε ≥ 0`; `μ ∈ [0, 1]` is automatic. -/
theorem lemma_10 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → ℝ) (hmeas : ∀ t, Measurable (x t))
    (hindep : iIndepFun x P) (h01 : ∀ t, ∀ᵐ ω ∂P, x t ω = 0 ∨ x t ω = 1)
    (μ : ℝ) (hmean : ∀ t, ∫ ω, x t ω ∂P = μ) :
    (∀ ε : ℝ, 0 < μ → μ < 1 → 0 < ε → μ + ε < 1 →
      P.real {ω | (∑ t, x t ω) / n - μ ≥ ε} ≤ Real.exp (-(n : ℝ) * klBern (μ + ε) μ)) ∧
    (∀ ε : ℝ, 0 < μ → μ < 1 → 0 < ε → 0 < μ - ε →
      P.real {ω | (∑ t, x t ω) / n - μ ≤ -ε} ≤ Real.exp (-(n : ℝ) * klBern (μ - ε) μ)) ∧
    (∀ ε : ℝ, 0 ≤ ε →
      P.real {ω | |(∑ t, x t ω) / n - μ| ≥ ε} ≤ 2 * Real.exp (-2 * (n : ℝ) * ε ^ 2)) := by sorry

end BayesBAI
