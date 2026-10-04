-- Prove2me | Theorems.Thm_AgrawalGoyalTS_TwoArmed_thompson_sampling_two_armed_regret
-- name    : AgrawalGoyalTS.TwoArmed.thompson_sampling_two_armed_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:28:26.015989+00:00
-- url     : https://prove2.me/theorems/98412e77-867b-4664-95e4-c931600b0e74
-- title:
--   Theorem 1 — Thompson Sampling has O(ln T/Δ + 1/Δ³) regret on two arms
-- statement:
--   Consider the two-armed stochastic bandit problem: arm $i\in\{1,2\}$ has a fixed reward distribution supported in $[0,1]$ with mean $\mu_i$, and arm 1 is the unique optimal arm, $\mu_1>\mu_2$. Let $\Delta=\mu_1-\mu_2$, and let $\mathbb E[\mathcal R(T)]=\mathbb E\big[\sum_{t=1}^T(\mu_1-\mu_{i(t)})\big]$ be the expected regret in time $T$ of Thompson Sampling for general stochastic bandits (Algorithm 2). There is an absolute constant $C>0$ such that for every such instance and every $T\ge 2$,
--   $$\mathbb E[\mathcal R(T)]\le C\Big(\frac{\ln T}{\Delta}+\frac{1}{\Delta^3}\Big).$$
--
--   This is the first logarithmic finite-time regret bound for Thompson Sampling; its dependence on $T$ matches the Lai–Robbins lower bound up to constants.
--
--   **Formalization Note** The paper writes $\mathbb E[\mathcal R(T)]=O(\ln T/\Delta+1/\Delta^3)$ in the sense of its footnote 1; we state it with one universal constant $C$, quantified before the reward distributions, the means and $T$, and for every $T\ge 2$. The paper's explicit display on p. 8 ($40\ln T/\Delta+48/\Delta^3+18\Delta$) is not the formal claim, because its derivation contains an arithmetic slip. Arm 1 of the paper is Lean arm `0`; no condition $\mu_1<1$ or $\mu_2>0$ is assumed.
-- source:
--   Agrawal and Goyal, Analysis of Thompson Sampling for the Multi-armed Bandit Problem, arXiv:1111.1797v3, p. 3, Theorem 1 (O(·) as in footnote 1, p. 4; proof in §3, pp. 6–8)

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_AgrawalGoyalTS_TwoArmed_ThompsonSampling

open MeasureTheory BanditAlgorithm

namespace AgrawalGoyalTS.TwoArmed

/-- Theorem 1 (p. 3): there is an absolute constant `C > 0` such that for every two-armed
stochastic bandit with rewards supported in `[0,1]` and `μ₁ > μ₂` (arm `0` is the paper's arm 1),
and every horizon `T ≥ 2`, Thompson Sampling (Algorithm 2) has expected regret
`E[R(T)] ≤ C (ln T / Δ + 1 / Δ³)`, `Δ = μ₁ - μ₂`. -/
theorem thompson_sampling_two_armed_regret :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : StochasticBandit 2, (∀ i, ν.P i (Set.Icc 0 1) = 1) →
      banditArmMean ν 1 < banditArmMean ν 0 → ∀ T : ℕ, 2 ≤ T →
        tsRegret ν T ≤
          ENNReal.ofReal (C * (Real.log T / (banditArmMean ν 0 - banditArmMean ν 1) +
            1 / (banditArmMean ν 0 - banditArmMean ν 1) ^ 3)) := by sorry

end AgrawalGoyalTS.TwoArmed
