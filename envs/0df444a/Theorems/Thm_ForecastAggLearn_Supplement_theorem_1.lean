-- Prove2me | Theorems.Thm_ForecastAggLearn_Supplement_theorem_1
-- name    : ForecastAggLearn.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:43:35.702366+00:00
-- url     : https://prove2.me/theorems/9b256fba-b01b-4f47-9154-be1b400dc1ec
-- title:
--   Theorem 1 (corrected: $n\ge1$ in the rate) — a prior-ignorant aggregator learns the optimal aggregation in a static environment with regret $\tilde O(n\sigma^{-1}\sqrt T)$
-- statement:
--   **Setting.** A binary state $\omega\in\{0,1\}$ with prior $\mu=\mathbb P(\omega=1)\in[0,1]$; $m$ signals with values in measurable spaces $S_j$, conditionally independent given $\omega$; $n$ Bayesian experts, expert $i$ observing the signals in $A_i\subseteq[m]$ and reporting her posterior $F_i=\mathbb P(\omega=1\mid(s_j)_{j\in A_i})$; the evidence matrix $A\in\{0,1\}^{n\times m}$, $A(i,j)=1$ iff $j\in A_i$. In the **static environment** the same information structure $(A,C)$ (one prior $\mu$, one family of conditional signal laws) governs every period, and periods are independent. A **prior-ignorant aggregator** does not know $\mu$: in period $t$ it forecasts $r_t\in[0,1]$ from the forecast profiles $F_1,\dots,F_t$ and the past states $\omega_1,\dots,\omega_{t-1}$ only. Its **total regret** over $T$ periods is
--
--   $$
--   \sum_{t=1}^T\mathbb E\bigl[l(r_t,\omega_t)-l(r^*(s_t),\omega_t)\bigr],
--   $$
--
--   where $l$ is the logarithmic loss and $r^*(s_t)=\mathbb P(\omega_t=1\mid s_{t,1},\dots,s_{t,m})$ aggregates all signals (Definition 1).
--
--   **Theorem 1.**
--
--   1. *(Learning.)* For every $n$ there is $R:\mathbb N\to\mathbb R$ with $R(T)/T\to0$ such that for every $T$ some prior-ignorant aggregator has total regret at most $R(T)$ for every number of signals $m$, every injective evidence matrix $A$ with $n$ rows, all signal spaces, every prior $\mu\in[0,1]$ and all conditional signal laws.
--   2. *(Rate.)* There are absolute constants $c>0$ and $k\in\mathbb N$ such that for every $n\ge1$, every $\sigma>0$ and every $T\ge1$ some prior-ignorant aggregator has total regret at most
--
--   $$
--   R(T)=c\,n\,\sigma^{-1}\sqrt T\,(1+\ln T)^k=\tilde O\bigl(n\sigma^{-1}\sqrt T\bigr)
--   $$
--
--   for every $m$, every evidence matrix with $\sigma_{\min}(A)\ge\sigma$, all signal spaces, every prior $\mu\in[0,1]$ and all conditional laws.
--
--   This is the companion of Theorem 2: in a static environment the aggregator does not need to be told the prior. In a dynamic environment the prior-ignorant aggregator cannot learn (Proposition 2), and no aggregator can when $A$ is not injective (Proposition 1).
--
--   **Formalization Note** A prior-ignorant aggregator is a prior-aware one whose forecast does not change when the priors it is given are changed. The static environment is the dynamic one with constant sequences of priors and signal laws. The aggregator is chosen after $n$, $T$ (and $\sigma$) and before $m$, $A$, the signal spaces, the prior and the laws. The regret bound is stated as $\text{aggregator's total expected loss}\le\text{benchmark's}+R(T)$ in $[0,\infty]$. $\sigma_{\min}(A)\ge\sigma$ is encoded as $\sigma\|y\|\le\|Ay\|$ for all $y\in\mathbb R^m$. Periods are 0-based.
--
--   Differences from the source:
--   - correction: R(T) = Õ(nσ^{−1}√T) with no explicit nonempty-expert guard → clause 2 assumes 1 ≤ n; reason: at n = 0 (hence m = 0) the bound c·0·σ^{−1}·√T·(1 + ln T)^k is 0, but a prior-ignorant aggregator that sees nothing forecasts a fixed r_0 at t = 0 while r* = µ, so any µ ∈ (0, 1) with µ ≠ r_0 gives strictly positive regret (strict properness of the log loss); clause 1 keeps n = 0
--   - reading: R(T) = Õ(nσ^{−1}√T) → R(T) = c · n · σ^{−1} · √T · (1 + ln T)^k with absolute constants c > 0, k ∈ ℕ chosen before n, σ, T; reason: Õ hides polylogarithmic factors in T; the constants may not depend on n, σ, the instance or the prior (the strong reading, as in the published Theorem 2)
--   - generalization: "can learn": for an injective A, regret R(T) = o(T) → for each n one R with R(T)/T → 0 valid for every m and every injective n-row evidence matrix; reason: uniform in A, which implies the bound for each A; the injective 0/1 matrices with n rows are finitely many
--   - encoding: σ_min(A) ≥ σ > 0; σ_min(A)² = λ_min(AᵀA) → 0 < σ and σ‖y‖ ≤ ‖Ay‖ for all y ∈ ℝ^m; reason: the norm inequality is λ_min(AᵀA) ≥ σ² for m ≥ 1
--   - generalization: m ≥ 1 signals (implicit) → m = 0 allowed (the σ condition is then vacuous); reason: with no signals every expert reports µ = r*, so for n ≥ 1 echoing an expert has regret 0; in clause 1 with n = 0 a Krichevsky–Trofimov forecast of the past states has regret O(ln T) = o(T)
--   - encoding: prior µ ∈ Δ(Ω); F_i, r* by formulas (1)–(2) → µ ∈ [0, 1] including 0 and 1; F_i, r* as density posteriors (post); reason: the density form is defined for every µ and equals (1)–(2) where those are defined (published eq_1_2_formula)
--   - encoding: the prior-ignorant aggregator (an algorithm that does not know the prior) → a PriorAwareAggregator n T whose forecast is unchanged when its priors argument is replaced, i.e. a deterministic, jointly measurable, [0, 1]-valued function of the forecast profiles and past states; reason: the information constraint of pp.2 and 10 as a type plus an explicit independence condition; restricting the rules only strengthens the existence claim
--   - encoding: static environment: one structure (A, C) for all periods; Σ_t E[l(r_t, ω_t) − l(r*(s_t), ω_t)] ≤ R(T) → dynamicLaw with the constant sequences fun _ => µ and fun _ => P (independent identically distributed periods); ∫⁻ Σ_t l(r_t, ω_t) ≤ ∫⁻ Σ_t l(r*(s_t), ω_t) + R(T); reason: avoids ∞ − ∞ in ℝ≥0∞; periods independent as in the paper's model
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, Theorem 1, p.12; Definition 1 and §2 (static environment), p.10; proof §4.3, pp.21–23

import Mathlib
import Definitions.Def_ForecastAggLearn_evidenceMatrix
import Definitions.Def_ForecastAggLearn_PriorAwareAggregator
import Definitions.Def_ForecastAggLearn_aggregatorLoss
import Definitions.Def_ForecastAggLearn_benchmarkLoss

namespace ForecastAggLearn.Supplement

open MeasureTheory Filter Topology

universe u

/-- **Theorem 1: a prior-ignorant aggregator learns the optimal aggregation in a static
environment, with regret `Õ(nσ^{−1}√T)`.**
Babichenko, Garber, arXiv:1802.07107v1, Theorem 1, p.12: "In case A is injective, the
prior-ignorant aggregator can learn the optimal aggregation in a static environment. Moreover, for
the class of information structures (A, C) such that σ_min(A) ≥ σ > 0, the prior-ignorant
aggregator can guarantee a total regret of R(T) = Õ(nσ^{−1}√T) within T periods." "Guarantee" and
"learn" are Definition 1, p.10; the static environment is §2, p.10.

1. For every number of experts `n` there is `R` with `R(T)/T → 0` such that, for every horizon
   `T`, some prior-ignorant aggregator has total expected regret at most `R(T)` against the
   Bayes-optimal forecast `r*`, for every number of signals `m`, every injective evidence matrix
   with `n` rows, all signal spaces, every prior `µ ∈ [0, 1]` and all conditional signal laws,
   the same in every period.
2. There are absolute constants `c > 0` and `k` such that for every `n ≥ 1`, every `σ > 0` and
   every `T ≥ 1`, some prior-ignorant aggregator has total expected regret at most
   `c · n · σ^{−1} · √T · (1 + ln T)^k` on every such static instance with `σ_min(A) ≥ σ`.

**Formalization Note.** A prior-ignorant aggregator is a `PriorAwareAggregator n T` whose forecast
does not depend on its priors argument (the first conjunct after `∃ alg`): it uses the forecast
profiles and the past states only. The static environment is the base `dynamicLaw` with the
constant sequences `fun _ => μ` and `fun _ => P`. The aggregator is chosen after `n` (and `σ`) and
`T` only, before `m`, the evidence matrix, the signal spaces, the prior and the laws. Regret is
additive, `aggregatorLoss ≤ benchmarkLoss + R`, in `ℝ≥0∞`. `Õ` is read as
`c n σ^{−1} √T (1 + ln T)^k` with absolute `c, k`. `σ_min(A) ≥ σ` is `σ‖y‖ ≤ ‖Ay‖` for all `y`.
`1 ≤ n` in clause 2 excludes the empty panel: with no experts the bound reads `0`, while an
aggregator that sees nothing and does not know `µ` has positive regret. Periods are 0-based. -/
theorem theorem_1 :
    (∀ n : ℕ, ∃ R : ℕ → ℝ, Tendsto (fun T : ℕ => R T / T) atTop (𝓝 0) ∧
      ∀ T : ℕ, ∃ alg : PriorAwareAggregator n T,
        (∀ (t : Fin T) (μs μs' : Fin (t.val + 1) → ℝ) (Fs : Fin (t.val + 1) → Fin n → ℝ)
            (ωs : Fin t.val → Bool), alg.forecast t μs Fs ωs = alg.forecast t μs' Fs ωs) ∧
        ∀ (m : ℕ) (Aset : Fin n → Finset (Fin m)),
          Function.Injective (evidenceMatrix Aset).mulVec →
          ∀ (S : Fin m → Type u) [∀ j, MeasurableSpace (S j)] (μ : ℝ)
            (P : (j : Fin m) → Bool → Measure (S j)),
            μ ∈ Set.Icc (0 : ℝ) 1 → (∀ j b, IsProbabilityMeasure (P j b)) →
            aggregatorLoss alg Aset (fun _ => μ) (fun _ => P) ≤
              benchmarkLoss T (fun _ => μ) (fun _ => P) + ENNReal.ofReal (R T)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ k : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ σ : ℝ, 0 < σ → ∀ T : ℕ, 1 ≤ T →
      ∃ alg : PriorAwareAggregator n T,
        (∀ (t : Fin T) (μs μs' : Fin (t.val + 1) → ℝ) (Fs : Fin (t.val + 1) → Fin n → ℝ)
            (ωs : Fin t.val → Bool), alg.forecast t μs Fs ωs = alg.forecast t μs' Fs ωs) ∧
        ∀ (m : ℕ) (Aset : Fin n → Finset (Fin m)),
          (∀ y : EuclideanSpace ℝ (Fin m), σ * ‖y‖ ≤
            ‖(WithLp.toLp 2 ((evidenceMatrix Aset).mulVec y.ofLp) : EuclideanSpace ℝ (Fin n))‖) →
          ∀ (S : Fin m → Type u) [∀ j, MeasurableSpace (S j)] (μ : ℝ)
            (P : (j : Fin m) → Bool → Measure (S j)),
            μ ∈ Set.Icc (0 : ℝ) 1 → (∀ j b, IsProbabilityMeasure (P j b)) →
            aggregatorLoss alg Aset (fun _ => μ) (fun _ => P) ≤
              benchmarkLoss T (fun _ => μ) (fun _ => P) +
                ENNReal.ofReal (c * n / σ * Real.sqrt T * (1 + Real.log T) ^ k)) := by sorry

end ForecastAggLearn.Supplement
