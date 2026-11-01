-- Prove2me | Theorems.Thm_CompetingAgents_theorem_17
-- name    : CompetingAgents.theorem_17
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:23:30.539012+00:00
-- url     : https://prove2.me/theorems/ad1c48c5-f093-4964-8cc0-36df10bd9b77
-- title:
--   Theorem 17 — sample-quantile concentration $P(|\hat\theta_p-\theta_p|>\epsilon)\le4e^{-2nM_\epsilon^2}$ (Shao, Theorem 5.9)
-- statement:
--   Let $X_1,\dots,X_n$ be i.i.d. real random variables with distribution function $F$, and let $p\in(0,1)$. Let $\theta_p$ be the $p$-th quantile of $F$ and $\hat\theta_p$ the $p$-th quantile of the empirical distribution function $F_n$. Suppose $p<F(\theta_p+\epsilon)$ for every $\epsilon>0$. Then for every $\epsilon>0$,
--
--   $$P\big(|\hat\theta_p-\theta_p|>\epsilon\big)\le4e^{-2nM_\epsilon^2},\qquad M_\epsilon=\min\{F(\theta_p+\epsilon)-p,\;p-F(\theta_p-\epsilon)\}.$$
--
--   This classical bound (Shao 2003, Theorem 5.9) is the probabilistic input of Lemma 3.
--
--   **Formalization Note** Quantiles are lower quantiles. The $X_i$ are measurable functions on a probability space, independent, each with law $\nu$, and $F$ is the distribution function of $\nu$. At $n=0$ the bound is $4$.
--
--   Differences from the source:
--
--   - reading: the $q$-th quantile $q(\cdot)$ → the lower quantile $\inf\{r : q\le G(r)\}$; reason: the convention of Shao (2003), cited for Theorem 17; for $P(\beta,s)$ it is the unique inverse of Lemma 30
--   - encoding: $p$ is not restricted → $0<p<1$; reason: only $p\in(0,1)$ gives a real $p$-th quantile; the hypothesis excludes only undefined cases
--   - encoding: $X_1,\dots,X_n$ i.i.d. from a CDF $F$ → measurable, independent $X_i$ on a probability space, each with law $\nu$, $F$ the distribution function of $\nu$; reason: the standard meaning of an i.i.d. sample
-- source:
--   Sahoo, Wager, Policy Learning with Competing Agents, arXiv:2204.01884v5, Theorem 17, p.30 (citing Shao 2003, Theorem 5.9)

import Mathlib
import Definitions.Def_CompetingAgents_quantile

open MeasureTheory ProbabilityTheory

namespace CompetingAgents

/-- Theorem 17 (Sahoo, Wager, *Policy Learning with Competing Agents*, arXiv:2204.01884v5,
Theorem 17, p.30, citing Shao, *Mathematical Statistics* (2003), Theorem 5.9). Let
`X₁, …, Xₙ` be i.i.d. random variables with distribution function `F`. Let `θ_p` be the `p`-th
quantile of `F` and `θ̂_p` the `p`-th quantile of the empirical distribution function `Fₙ`. Suppose
`p < F(θ_p + ε)` for every `ε > 0`. Then for every `ε > 0`,
`P(|θ̂_p − θ_p| > ε) ≤ 4 exp(−2n M_ε²)`, where `M_ε = min{F(θ_p + ε) − p, p − F(θ_p − ε)}`.

**Formalization Note.** Quantiles are lower quantiles `inf {r : p ≤ G r}` (`quantile`), and
`0 < p < 1`, where the quantile of `F` is a real number. The `Xᵢ` are measurable, independent and
each has law `ν` (a probability measure on `ℝ` with distribution function `F = cdf ν`). At `n = 0` the
bound is `4` and holds trivially. -/
theorem theorem_17 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {n : ℕ} (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ) (hlaw : ∀ i, μ.map (X i) = ν)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hF : ∀ ε : ℝ, 0 < ε → p < cdf ν (quantile p (cdf ν) + ε))
    (ε : ℝ) (hε : 0 < ε) :
    let θ := quantile p (cdf ν)
    let Mε := min (cdf ν (θ + ε) - p) (p - cdf ν (θ - ε))
    μ {ω | ε < |quantile p (empiricalCDF fun i => X i ω) - θ|} ≤
      ENNReal.ofReal (4 * Real.exp (-2 * n * Mε ^ 2)) := by sorry

end CompetingAgents
