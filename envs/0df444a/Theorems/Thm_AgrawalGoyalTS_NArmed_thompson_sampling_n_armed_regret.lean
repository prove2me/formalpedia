-- Prove2me | Theorems.Thm_AgrawalGoyalTS_NArmed_thompson_sampling_n_armed_regret
-- name    : AgrawalGoyalTS.NArmed.thompson_sampling_n_armed_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:48:24.130131+00:00
-- url     : https://prove2.me/theorems/e20c3d4e-227a-4e47-92ef-5289128677b2
-- title:
--   Theorem 2 — Thompson Sampling has regret O((Σ_a 1/Δ_a²)² ln T) on N arms
-- statement:
--   Consider the $N$-armed stochastic bandit problem, $N\ge2$: arm $i$ yields i.i.d. rewards from a fixed distribution supported in $[0,1]$ with mean $\mu_i$, and arm $1$ is the unique optimal arm, $\mu_1>\mu_i$ for $i\ne1$. Let $\Delta_a=\mu_1-\mu_a$. There is an absolute constant $C>0$ such that for every such instance and every horizon $T\ge2$, Thompson Sampling for general stochastic bandits (Algorithm 2) has expected regret
--
--   $$\mathbb E[\mathcal R(T)]\le C\Big(\sum_{a=2}^{N}\frac{1}{\Delta_a^2}\Big)^2\ln T .$$
--
--   This is the first logarithmic regret bound for Thompson Sampling with more than two arms; its dependence on $T$ matches the Lai–Robbins lower bound up to constants.
--
--   **Formalization Note** The paper writes $O(\cdot)$ in the sense of its footnote 1; it is stated here with a single universal constant $C$, chosen before the number of arms, the reward distributions and the horizon, so $C$ depends on none of them, and the bound holds for every $T\ge2$. The explicit constants of App. D are not formalized: the chain that produces them contains arithmetic slips, while the $O(\cdot)$ claim does not depend on them. At $T=1$ the right side is $0$ while the regret can be positive, so $T\ge2$ is part of the statement. Lean arm $0$ is the paper's arm $1$; the regret is $\mathbb E[\sum_{t=1}^T(\mu^*-\mu_{i(t)})]$ under the law of the algorithm's run, defined in the ThompsonSampling file.
-- source:
--   Agrawal and Goyal, Analysis of Thompson Sampling for the Multi-armed Bandit Problem, arXiv:1111.1797v3, pp. 3–4, Theorem 2 (footnote 1, p. 4; proof in §4 and App. D, pp. 8–11, 20–21)

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_AgrawalGoyalTS_NArmed_ThompsonSampling

open MeasureTheory BanditAlgorithm

namespace AgrawalGoyalTS.NArmed

/-- Theorem 2 (pp. 3–4): there is an absolute constant `C > 0` such that for every number of
arms `N ≥ 2`, every `N`-armed stochastic bandit with rewards supported in `[0,1]` in which arm
`0` (the paper's arm 1) is the unique optimal arm, and every horizon `T ≥ 2`, Thompson Sampling
(Algorithm 2) has expected regret `E[R(T)] ≤ C (∑_{a ≠ 1} 1/Δ_a²)² ln T`, `Δ_a = μ_1 - μ_a`. -/
theorem thompson_sampling_n_armed_regret :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N], 2 ≤ N → ∀ ν : StochasticBandit N,
      (∀ i, ν.P i (Set.Icc 0 1) = 1) →
      (∀ i, i ≠ 0 → banditArmMean ν i < banditArmMean ν 0) → ∀ T : ℕ, 2 ≤ T →
        AgrawalGoyalTS.TwoArmed.tsRegret ν T ≤
          ENNReal.ofReal (C * (∑ a ∈ Finset.univ.filter (fun a : Fin N => a ≠ 0),
            1 / gapTo0 ν a ^ 2) ^ 2 * Real.log T) := by sorry

end AgrawalGoyalTS.NArmed
