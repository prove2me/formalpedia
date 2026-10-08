-- Prove2me | Theorems.Thm_AgrawalGoyalTS_NArmed_prob_eventE_ge
-- name    : AgrawalGoyalTS.NArmed.prob_eventE_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T18:06:04.155986+00:00
-- url     : https://prove2.me/theorems/26cf5336-e493-4468-90a0-30df44985b70
-- title:
--   Lemma 4 — Pr(E(t)) ≥ 1 − 4(N−1)/T², also conditionally on s(j)
-- statement:
--   Consider Thompson Sampling (Algorithm 2) on $N$ arms whose reward distributions are supported in $[0,1]$, where arm $1$ is the unique optimal arm: $\mu_1>\mu_i$ for all $i\ne1$. Fix the horizon $T$, let $\Delta_i=\mu_1-\mu_i$, $L_i=24\ln T/\Delta_i^2$, $C(t)=\{i\ne1:k_i(t)\ge L_i\}$ the saturated arms, and
--   $$E(t):\ \theta_i(t)\in\Big[\mu_i-\frac{\Delta_i}{2},\ \mu_i+\frac{\Delta_i}{2}\Big]\ \text{ for all } i\in C(t).$$
--   Let $s(j)$ be the number of successes in the first $j$ plays of arm $1$. Then for every round $t=1,\dots,T$,
--
--   $$\Pr(E(t))\ge 1-\frac{4(N-1)}{T^2},$$
--
--   and for all $t$, all $j$ and all $s\le j$,
--
--   $$\Pr\big(E(t)\cap\{s(j)=s\}\big)\ge\Big(1-\frac{4(N-1)}{T^2}\Big)\Pr\big(s(j)=s\big).$$
--
--   The second inequality is the paper's $\Pr(E(t)\mid s(j)=s)\ge1-4(N-1)/T^2$. The lemma says that the posterior samples of all saturated arms are concentrated around their means with high probability, uniformly in time; it controls the regret from rounds where a saturated arm's sample is an outlier.
--
--   **Formalization Note** The conditional bound is multiplied out by $\Pr(s(j)=s)$, which needs no positivity hypothesis and is equivalent to the paper's form whenever the conditional probability is defined (for instance when $0<\mu_1<1$). Lean round $t<T$ is the paper's round $t+1$. The probability space is the reward-stack model, in which $s(j)$ is defined for every $j$.
-- source:
--   Agrawal and Goyal, Analysis of Thompson Sampling for the Multi-armed Bandit Problem, arXiv:1111.1797v3, p. 9, Lemma 4 (proof in App. C.4, pp. 17–19)

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_AgrawalGoyalTS_NArmed_ThompsonSampling
import Definitions.Def_AgrawalGoyalTS_NArmed_Saturation

open MeasureTheory BanditAlgorithm

namespace AgrawalGoyalTS.NArmed

/-- Lemma 4 (p. 9): `N` arms with rewards supported in `[0,1]`, arm `0` (the paper's arm 1) the
unique optimal arm. For every round `t` of the horizon `T` (Lean rounds `t < T`),
`Pr(E(t)) ≥ 1 - 4(N-1)/T²`; and for all `j` and `s ≤ j`,
`Pr(E(t) | s(j) = s) ≥ 1 - 4(N-1)/T²`, written in the multiplied-out form
`Pr(E(t) ∩ {s(j) = s}) ≥ (1 - 4(N-1)/T²) Pr(s(j) = s)`. -/
theorem prob_eventE_ge {N : ℕ} [NeZero N] (ν : StochasticBandit N)
    (hsupp : ∀ i, ν.P i (Set.Icc 0 1) = 1)
    (hopt : ∀ i, i ≠ 0 → banditArmMean ν i < banditArmMean ν 0) (T t : ℕ) (ht : t < T) :
    ENNReal.ofReal (1 - 4 * ((N : ℝ) - 1) / (T : ℝ) ^ 2) ≤
        AgrawalGoyalTS.TwoArmed.tsLaw ν {ω | eventE ν T ω t} ∧
    ∀ j s : ℕ, s ≤ j →
      ENNReal.ofReal (1 - 4 * ((N : ℝ) - 1) / (T : ℝ) ^ 2) *
          AgrawalGoyalTS.TwoArmed.tsLaw ν {ω | stackSuccesses ω 0 j = s} ≤
        AgrawalGoyalTS.TwoArmed.tsLaw ν {ω | eventE ν T ω t ∧ stackSuccesses ω 0 j = s} := by sorry

end AgrawalGoyalTS.NArmed
