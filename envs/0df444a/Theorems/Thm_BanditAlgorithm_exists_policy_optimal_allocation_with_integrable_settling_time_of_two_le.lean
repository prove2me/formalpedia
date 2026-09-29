-- Prove2me | Theorems.Thm_BanditAlgorithm_exists_policy_optimal_allocation_with_integrable_settling_time_of_two_le
-- name    : BanditAlgorithm.exists_policy_optimal_allocation_with_integrable_settling_time_of_two_le
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-01T16:09:51.60483+00:00
-- url     : https://prove2.me/theorems/b5283542-08dd-486b-abda-770469fb9044
-- title:
--   Proposition 13, main case: two or more arms
-- statement:
--   **Proposition 13, for two or more arms.** There is a single sampling rule -- one policy, fixed before the environment and before the confidence level -- such that for every unit-variance Gaussian bandit with a strictly best arm there is an optimal allocation $\alpha^*$ of Lattimore--Szepesv\'ari Eq. (33.4), with all weights strictly positive, whose settling time
--   $$T_\xi=\inf\Big\{N\ \Big|\ \forall n\ge N,\ n\ge 1,\ \max_i|T_i(n)/n-\alpha^*_i|\le\xi\ \text{ and }\ \max_i|\hat\mu_i(n)-\mu_i|\le\xi\Big\}$$
--   is almost surely finite and satisfies $\mathbb E[T_\xi]<\infty$, at every accuracy $\xi>0$.
--
--   The integrability, not merely the almost-sure finiteness, is the content: almost-sure convergence of the empirical allocation does not bound $\mathbb E[\tau_\delta]$, since a rule may delay an arm to a round that is finite almost surely but has infinite mean.
--
--   For D-Tracking the quantitative input is the forced-exploration floor, which gives $T_j(t)\ge\sqrt{k^2+t}-2k+1$ deterministically and hence Gaussian deviations at $\asymp\sqrt t$ samples. Continuity of $\alpha^*$ at $\mu$ -- available from uniqueness of the optimal allocation, with no modulus needed -- transfers this to the allocation through the tracking bound $|T_i(t)-\sum_{s<t}p_i(s)|\le k$ and a Cesàro average.
--
--   Two arms are needed for the statement to have content: the objective $\Psi_i(\mu,\alpha)=\min_{j\ne i}(\cdot)$ is an infimum over an empty index set when $k=1$.
-- source:
--   Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, Proposition 13; Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Algorithm 21 and the proof of Theorem 33.6.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem BanditAlgorithm.exists_policy_optimal_allocation_with_integrable_settling_time_of_two_le
    {k : ℕ} [NeZero k] (hk2 : 2 ≤ k) :
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
