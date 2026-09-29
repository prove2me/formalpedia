-- Prove2me | Theorems.Thm_BanditAlgorithm_exists_policy_optimal_allocation_with_integrable_settling_time_of_subsingleton
-- name    : BanditAlgorithm.exists_policy_optimal_allocation_with_integrable_settling_time_of_subsingleton
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-01T16:10:16.407828+00:00
-- url     : https://prove2.me/theorems/0e620da0-7396-49a8-b3a8-7cacc79a24c3
-- title:
--   Proposition 13, degenerate case: at most one arm
-- statement:
--   **Proposition 13, for a single arm.** The degenerate case of the previous statement, separated because the plug-in allocation maximises an infimum over an empty index set when there is only one arm.
--
--   With one arm there is nothing to identify. The arm space is a subsingleton, so *every* trajectory plays the only arm at every round and the pull counts are $T_0(t)=t$ identically -- no measure theory is involved. Consequently the forced-exploration bound holds for every trajectory, and the empirical allocation is $T_0(n)/n=1$ exactly from round one on, so its settling time is $1$ rather than merely integrable. Only the empirical mean needs the time-uniform deviation bound.
--
--   The unique probability vector on one arm is the point mass, which is strictly positive, so the package the general statement asks for is available here too.
-- source:
--   Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, Proposition 13; Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Algorithm 21 and the proof of Theorem 33.6.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem BanditAlgorithm.exists_policy_optimal_allocation_with_integrable_settling_time_of_subsingleton
    {k : ℕ} [NeZero k] (hk1 : ∀ i j : Fin k, i = j) :
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
