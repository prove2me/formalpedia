-- Prove2me | Theorems.Thm_AgrawalGoyalTS_TwoArmed_expected_plays_arm_two_le
-- name    : AgrawalGoyalTS.TwoArmed.expected_plays_arm_two_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:27:54.322582+00:00
-- url     : https://prove2.me/theorems/1e6a290a-bdc5-4599-a844-7e5526ad07c0
-- title:
--   Eq. (1) — E[k₂(T)] = O(ln T/Δ² + 1/Δ⁴), universal-constant form
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let a two-armed stochastic bandit have reward distributions supported in $[0,1]$ with means $\mu_1>\mu_2$, and let $\Delta=\mu_1-\mu_2$. For every horizon $T\ge 2$, the expected number $\mathbb E[k_2(T)]$ of plays of the suboptimal arm in the first $T$ rounds of Thompson Sampling (Algorithm 2) satisfies
--   $$\mathbb E[k_2(T)]\le C\Big(\frac{\ln T}{\Delta^2}+\frac{1}{\Delta^4}\Big).$$
--
--   The paper's Eq. (1) reports $\mathbb E[k_2(T)]\le 40\ln T/\Delta^2+48/\Delta^4+18$; multiplied by $\Delta$ it gives Theorem 1.
--
--   **Formalization Note** The printed numerals are not part of the formal claim: the derivation in App. C.3 (p. 16) has an arithmetic slip in the $1/\Delta^4$ term and treats the real threshold $L=24\ln T/\Delta^2$ as an integer count. The statement uses one universal constant, quantified before the instance and the horizon; the additive $18$ is absorbed since $\Delta\le 1$. $k_2(T)$ is taken as the number of plays in rounds $1,\dots,T$ (the paper calls it "the expected number of plays of the second arm in time $T$").
-- source:
--   Agrawal and Goyal, Analysis of Thompson Sampling for the Multi-armed Bandit Problem, arXiv:1111.1797v3, p. 7, Eq. (1) (details in App. C.3, p. 16)

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_AgrawalGoyalTS_TwoArmed_ThompsonSampling

open MeasureTheory BanditAlgorithm

namespace AgrawalGoyalTS.TwoArmed

/-- Eq. (1) (p. 7), universal-constant form: there is an absolute constant `C > 0` such that for
every two-armed instance with rewards in `[0,1]` and `μ₁ > μ₂` (arm `0` is the paper's arm 1),
and every `T ≥ 2`, the expected number of plays of the suboptimal arm in the first `T` rounds of
Thompson Sampling is at most `C (ln T / Δ² + 1 / Δ⁴)`, `Δ = μ₁ - μ₂`. -/
theorem expected_plays_arm_two_le :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : StochasticBandit 2, (∀ i, ν.P i (Set.Icc 0 1) = 1) →
      banditArmMean ν 1 < banditArmMean ν 0 → ∀ T : ℕ, 2 ≤ T →
        ∫⁻ ω, (tsPlays ω T 1 : ENNReal) ∂(tsLaw ν) ≤
          ENNReal.ofReal (C * (Real.log T / (banditArmMean ν 0 - banditArmMean ν 1) ^ 2 +
            1 / (banditArmMean ν 0 - banditArmMean ν 1) ^ 4)) := by sorry

end AgrawalGoyalTS.TwoArmed
