-- Prove2me | Theorems.Thm_ForecastAggLearn_theorem_2
-- name    : ForecastAggLearn.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:36.088133+00:00
-- url     : https://prove2.me/theorems/77180864-a12a-466c-a75b-dc1e1765c0d7
-- title:
--   Theorem 2 — a prior-aware aggregator learns the optimal aggregation in a dynamic environment with regret $\tilde O(n\sigma^{-1}\sqrt T)$
-- statement:
--   **Setting.** A binary state $\omega\in\{0,1\}$; $m$ signals with values in measurable spaces $S_j$, conditionally independent given $\omega$; $n$ Bayesian experts, expert $i$ observing the signals in $A_i\subseteq[m]$ and reporting her posterior $F_i=\mathbb P(\omega=1\mid(s_j)_{j\in A_i})$; the evidence matrix $A\in\{0,1\}^{n\times m}$, $A(i,j)=1$ iff $j\in A_i$. In the **dynamic environment** $A$ is fixed while period $t$ has its own prior $\mu_t\in[0,1]$ and conditional signal laws $C_{t,j}^\omega$; periods are independent. A **prior-aware aggregator** forecasts $r_t\in[0,1]$ from $\mu_1,\dots,\mu_t$, the forecast profiles $F_1,\dots,F_t$ and the past states $\omega_1,\dots,\omega_{t-1}$ only. Its **total regret** over $T$ periods is
--
--   $$
--   \sum_{t=1}^T\mathbb E\bigl[l(r_t,\omega_t)-l(r^*(s_t),\omega_t)\bigr],
--   $$
--
--   where $l$ is the logarithmic loss and $r^*(s_t)=\mathbb P(\omega_t=1\mid s_{t,1},\dots,s_{t,m})$ aggregates all signals (Definition 1).
--
--   **Theorem 2.**
--
--   1. *(Learning.)* For every $n$ there is $R:\mathbb N\to\mathbb R$ with $R(T)/T\to0$ such that for every $T$ some prior-aware aggregator has total regret at most $R(T)$ for every number of signals $m$, every injective evidence matrix $A$ with $n$ rows, all signal spaces, and all sequences of priors and conditional signal laws.
--   2. *(Rate.)* There are absolute constants $c>0$ and $k\in\mathbb N$ such that for every $n$, every $\sigma>0$ and every $T\ge1$ some prior-aware aggregator has total regret at most
--
--   $$
--   R(T)=c\,n\,\sigma^{-1}\sqrt T\,(1+\ln T)^k=\tilde O\bigl(n\sigma^{-1}\sqrt T\bigr)
--   $$
--
--   for every $m$, every evidence matrix with $\sigma_{\min}(A)\ge\sigma$, all signal spaces, and all sequences of priors and conditional laws.
--
--   The aggregator never sees the signals, the signal laws or $A$, and competes with the Bayes posterior given all the evidence, not with the best expert. The prior-ignorant aggregator cannot achieve this in the dynamic environment (Proposition 2), and no aggregator can when $A$ is not injective (Proposition 1).
--
--   **Formalization Note** The aggregator is chosen after $n$, $T$ (and $\sigma$) and before $m$, $A$, the signal spaces, the priors and the laws; its type gives it exactly the information above. The regret bound is stated as $\text{aggregator's total expected loss}\le\text{benchmark's}+R(T)$ in $[0,\infty]$. $\sigma_{\min}(A)\ge\sigma$ is encoded as $\sigma\|y\|\le\|Ay\|$ for all $y\in\mathbb R^m$. Periods are 0-based.
--
--   Differences from the source:
--   - reading: R(T) = Õ(nσ^{−1}√T) → R(T) = c · n · σ^{−1} · √T · (1 + ln T)^k with absolute constants c > 0, k ∈ ℕ chosen before n, σ, T; reason: Õ hides polylogarithmic factors in T; the constants may not depend on n, σ, the instance or the prior (the strong reading)
--   - generalization: "can learn": for an injective A, regret R(T) = o(T) → for each n one R with R(T)/T → 0 valid for every m and every injective n-row evidence matrix; reason: uniform in A, which implies the bound for each A; true since the injective 0/1 matrices with n rows are finitely many
--   - encoding: σ_min(A) ≥ σ (no σ > 0 printed); σ_min(A)² = λ_min(AᵀA) → 0 < σ and σ‖y‖ ≤ ‖Ay‖ for all y ∈ ℝ^m; reason: σ^{−1} appears in the bound; the norm inequality is λ_min(AᵀA) ≥ σ² for m ≥ 1
--   - generalization: m ≥ 1 signals (implicit) → m = 0 allowed (the σ condition is then vacuous); reason: with no signals every forecast and r* equal μ_t, and forecasting μ_t has regret 0
--   - encoding: priors µ_t ∈ Δ(Ω); F_i, r* by formulas (1)–(2) → µ_t ∈ [0, 1] including 0 and 1; F_i, r* as density posteriors (post); reason: the density form is defined for every µ_t and equals (1)–(2) where those are defined (eq_1_2_formula)
--   - encoding: an algorithm for the aggregator → a deterministic, jointly measurable, [0, 1]-valued rule of type PriorAwareAggregator n T; reason: the information constraint of p.10 and p.16 as a type; restricting the rules only strengthens the existence claim
--   - encoding: Σ_t E[l(r_t, ω_t) − l(r*(s_t), ω_t)] ≤ R(T); a sequence (A, C_t)_t → ∫⁻ Σ_t l(r_t, ω_t) ≤ ∫⁻ Σ_t l(r*(s_t), ω_t) + R(T) under the product of the T period laws, signal spaces fixed over t; reason: avoids ∞ − ∞ in ℝ≥0∞; periods independent and the sequence fixed in advance as in the paper's model
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, Theorem 2, p.13; Definition 1, p.10; proof §4.2, pp.16–21 and Appendix A, pp.27–28

import Mathlib
import Definitions.Def_ForecastAggLearn_evidenceMatrix
import Definitions.Def_ForecastAggLearn_PriorAwareAggregator
import Definitions.Def_ForecastAggLearn_aggregatorLoss
import Definitions.Def_ForecastAggLearn_benchmarkLoss

namespace ForecastAggLearn

open MeasureTheory Filter Topology

universe u

/-- **Theorem 2: a prior-aware aggregator learns the optimal aggregation in a dynamic
environment, with regret `Õ(nσ^{−1}√T)`.**
Babichenko, Garber, arXiv:1802.07107v1, Theorem 2, p.13: "In case A is injective, the
prior-aware aggregator can learn the optimal aggregation in a dynamic environment. Moreover, for
the class of information structures (A, C) such that σ_min(A) ≥ σ the prior-aware aggregator can
guarantee a total regret of R(T) = Õ(nσ^{−1}√T) within T periods." "Guarantee" and "learn" are
Definition 1, p.10.

1. For every number of experts `n` there is `R` with `R(T)/T → 0` such that, for every horizon
   `T`, some prior-aware aggregator has total expected regret at most `R(T)` against the
   Bayes-optimal forecast `r*`, for every number of signals `m`, every injective evidence matrix
   with `n` rows, all signal spaces, and all sequences of priors `µ_t ∈ [0, 1]` and conditional
   signal laws.
2. There are absolute constants `c > 0` and `k` such that for every `n`, every `σ > 0` and every
   `T ≥ 1`, some prior-aware aggregator has total expected regret at most
   `c · n · σ^{−1} · √T · (1 + ln T)^k` on every such instance with `σ_min(A) ≥ σ`.

**Formalization Note.** The aggregator (`PriorAwareAggregator n T`) is chosen after `n` (and `σ`)
and `T` only, before `m`, the evidence matrix, the signal spaces, priors and laws; its type gives
it the priors, the forecast profiles and the past states only. Regret is stated additively,
`aggregatorLoss ≤ benchmarkLoss + R`, in `ℝ≥0∞`. `Õ` is read as `c n σ^{−1} √T (1 + ln T)^k` with
absolute `c, k`. `σ_min(A) ≥ σ` is `σ‖y‖ ≤ ‖Ay‖` for all `y`. Periods are 0-based. -/
theorem theorem_2 :
    (∀ n : ℕ, ∃ R : ℕ → ℝ, Tendsto (fun T : ℕ => R T / T) atTop (𝓝 0) ∧
      ∀ T : ℕ, ∃ alg : PriorAwareAggregator n T,
        ∀ (m : ℕ) (Aset : Fin n → Finset (Fin m)),
          Function.Injective (evidenceMatrix Aset).mulVec →
          ∀ (S : Fin m → Type u) [∀ j, MeasurableSpace (S j)] (μ : ℕ → ℝ)
            (P : ℕ → (j : Fin m) → Bool → Measure (S j)),
            (∀ t, μ t ∈ Set.Icc (0 : ℝ) 1) → (∀ t j b, IsProbabilityMeasure (P t j b)) →
            aggregatorLoss alg Aset μ P ≤ benchmarkLoss T μ P + ENNReal.ofReal (R T)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ k : ℕ, ∀ n : ℕ, ∀ σ : ℝ, 0 < σ → ∀ T : ℕ, 1 ≤ T →
      ∃ alg : PriorAwareAggregator n T,
        ∀ (m : ℕ) (Aset : Fin n → Finset (Fin m)),
          (∀ y : EuclideanSpace ℝ (Fin m), σ * ‖y‖ ≤
            ‖(WithLp.toLp 2 ((evidenceMatrix Aset).mulVec y.ofLp) : EuclideanSpace ℝ (Fin n))‖) →
          ∀ (S : Fin m → Type u) [∀ j, MeasurableSpace (S j)] (μ : ℕ → ℝ)
            (P : ℕ → (j : Fin m) → Bool → Measure (S j)),
            (∀ t, μ t ∈ Set.Icc (0 : ℝ) 1) → (∀ t j b, IsProbabilityMeasure (P t j b)) →
            aggregatorLoss alg Aset μ P ≤ benchmarkLoss T μ P +
              ENNReal.ofReal (c * n / σ * Real.sqrt T * (1 + Real.log T) ^ k)) := by sorry

end ForecastAggLearn
