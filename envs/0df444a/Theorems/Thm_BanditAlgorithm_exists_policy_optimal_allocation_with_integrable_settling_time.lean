-- Prove2me | Theorems.Thm_BanditAlgorithm_exists_policy_optimal_allocation_with_integrable_settling_time
-- name    : BanditAlgorithm.exists_policy_optimal_allocation_with_integrable_settling_time
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-01T14:29:40.112814+00:00
-- url     : https://prove2.me/theorems/e83025e3-8047-45c7-b34b-42a156c9d93c
-- title:
--   Garivier–Kaufmann Proposition 13: a rule with integrable settling time
-- statement:
--   **Proposition 13.** There is a single sampling rule -- one policy, chosen before the environment and before the confidence level -- such that for every unit-variance Gaussian bandit $\nu=\mathcal N(\mu,I)$ with a unique best arm there is an optimal allocation $\alpha^*$ of Lattimore--Szepesv\'ari Eq. (33.4), with all weights strictly positive, for which the following holds at every accuracy $\xi>0$. Writing
--   $$T_\xi=\inf\Big\{N\ \Big|\ \forall n\ge N,\ n\ge 1,\ \max_i|T_i(n)/n-\alpha^*_i|\le\xi\ \text{ and }\ \max_i|\hat\mu_i(n)-\mu_i|\le\xi\Big\},$$
--   the empirical allocation and the empirical means settle within $\xi$ almost surely, and $\mathbb E[T_\xi]<\infty$.
--
--   The integrability, not merely the almost-sure finiteness, is the whole content. Almost-sure convergence of the empirical allocation does **not** bound $\mathbb E[\tau_\delta]$: a rule may delay its second arm to round $M$, where $M$ is a function of the first reward with $M<\infty$ almost surely but $\mathbb E[M]=\infty$; while one arm is unplayed the generalised-likelihood-ratio statistic carries the factor $T_{\hat\imath}T_j/(T_{\hat\imath}+T_j)=0$ and so cannot cross any threshold, giving $\tau_\delta\ge M$ and $\mathbb E[\tau_\delta]=\infty$, and this uniformly in $\delta$. A node asserting the sample-complexity bound from almost-sure convergence alone was retired for exactly this reason.
--
--   For D-Tracking the quantitative input is the forced-exploration floor. Playing at each round an arm maximising the shortfall $\sum_{s<t}p_j(s)-T_j(t)$, with $p(s)=(1-k\varepsilon_s)\alpha^*(\hat\mu(s))+\varepsilon_s\mathbf 1$ and $\varepsilon_s=1/(2\sqrt{k^2+s})$, forces $T_j(t)\ge\sqrt{k^2+t}-2k+1$ for every arm deterministically, with no hypothesis on the estimates. Gaussian deviations at that many samples give $\mathbb P(\max_i|\hat\mu_i(t)-\mu_i|>\varepsilon)\le 2k\exp(-\tfrac12\varepsilon^2(\sqrt t-2k))$, which is summable against the extra factor $t$ that turns a tail sum into an expectation. Continuity of $\alpha^*$ at $\mu$ -- available from uniqueness of the optimal allocation, with no modulus needed, since $\varepsilon$ may depend on $\xi$ arbitrarily -- transfers this to the allocation through the tracking bound $|T_i(t)-\sum_{s<t}p_i(s)|\le k$.
-- source:
--   Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, Proposition 13 (and Section 2.2 for D-Tracking); Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Algorithm 21 and the proof of Theorem 33.6.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem BanditAlgorithm.exists_policy_optimal_allocation_with_integrable_settling_time
    {k : ℕ} [NeZero k] :
    ∃ pol : BanditAlgorithm.BanditPolicy k,
      ∀ (μvec : Fin k → ℝ) (istar : Fin k),
        (∀ j, j ≠ istar → μvec j < μvec istar) →
        ∃ α : Fin k → NNReal,
          (∀ i, 0 < α i) ∧
          BanditAlgorithm.IsOptimalAllocation (BanditAlgorithm.gaussianBandit μvec)
              (Set.range (BanditAlgorithm.gaussianBandit (k := k))) α ∧
          ∀ ξ : ℝ, 0 < ξ →
          (∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure
              (BanditAlgorithm.gaussianBandit μvec) pol),
              ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
                (0 < n ∧
              (∀ i, |BanditAlgorithm.trajAllocation i n ω - (α i : ℝ)| ≤ ξ) ∧
              (∀ i, |BanditAlgorithm.trajEmpiricalMean i n ω - μvec i| ≤ ξ))) ∧
            ∫⁻ ω, ((sInf {N : ℕ | ∀ n, N ≤ n →
                (0 < n ∧
              (∀ i, |BanditAlgorithm.trajAllocation i n ω - (α i : ℝ)| ≤ ξ) ∧
              (∀ i, |BanditAlgorithm.trajEmpiricalMean i n ω - μvec i| ≤ ξ))} : ℕ) : ℝ≥0∞)
              ∂(BanditAlgorithm.banditTrajMeasure
                (BanditAlgorithm.gaussianBandit μvec) pol) ≠ ⊤ := by
  sorry
