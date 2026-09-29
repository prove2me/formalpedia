-- Prove2me | Theorems.Thm_BanditAlgorithm_settling_of_allocation_half_and_forced_exploration
-- name    : BanditAlgorithm.settling_of_allocation_half_and_forced_exploration
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-01T16:35:23.213844+00:00
-- url     : https://prove2.me/theorems/d343247e-2a2c-4b8e-b70a-8d62ab9f8a02
-- title:
--   Forced exploration plus a settling allocation gives a settling time
-- statement:
--   Let a sampling rule satisfy, almost surely, the forced-exploration bound $T_j(t)\ge\sqrt t-2k$ for every round and arm. Suppose that at accuracy $\xi$ the empirical allocation settles to $\alpha$ almost surely and its failure series is summable,
--   $$\sum_{m}(m+1)\,\mathbb P\big(\text{allocation off by more than }\xi\text{ at round }m\big)<\infty .$$
--   Then the *joint* settling time of the allocation and the empirical means,
--   $$T_\xi=\inf\Big\{N\ \Big|\ \forall n\ge N,\ n\ge 1,\ \max_i|T_i(n)/n-\alpha_i|\le\xi\ \text{ and }\ \max_i|\hat\mu_i(n)-\mu_i|\le\xi\Big\},$$
--   is almost surely finite and satisfies $\mathbb E[T_\xi]<\infty$.
--
--   This is Proposition 13 reduced to its allocation half: the empirical-mean half is supplied here, because forced exploration alone makes every mean rest on $\asymp\sqrt t$ samples and the time-uniform confidence bound then gives a summable failure series. The settling time of an intersection is at most the sum of the two, so integrability is inherited.
--
--   The count bound is assumed only almost surely, which is the strongest form any sampling rule delivers: a policy constrains only the trajectories in its support, while the canonical trajectory space contains every sequence of arm-reward pairs.
-- source:
--   Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, Proposition 13; Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), proof of Theorem 33.6.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem BanditAlgorithm.settling_of_allocation_half_and_forced_exploration
    {k : ℕ} [NeZero k] (μvec : Fin k → ℝ)
    (pol : BanditAlgorithm.BanditPolicy k) (α : Fin k → ℝ) {ξ : ℝ} (hξ : 0 < ξ)
    (hcount : ∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure
        (BanditAlgorithm.gaussianBandit μvec) pol),
      ∀ (t : ℕ) (j : Fin k),
        Real.sqrt (t : ℝ) - 2 * (k : ℝ) ≤ (BanditAlgorithm.trajPullCount j t ω : ℝ))
    (hAsettle : ∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure
        (BanditAlgorithm.gaussianBandit μvec) pol),
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (0 < n ∧ ∀ i, |BanditAlgorithm.trajAllocation i n ω - α i| ≤ ξ))
    (hAsum : ∑' m : ℕ, ((m : ℝ≥0∞) + 1) *
      BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ |
          0 < m ∧ ∀ i, |BanditAlgorithm.trajAllocation i m ω - α i| ≤ ξ}ᶜ ≠ ⊤) :
    (∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure
        (BanditAlgorithm.gaussianBandit μvec) pol),
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          (0 < n ∧
              (∀ i, |BanditAlgorithm.trajAllocation i n ω - α i| ≤ ξ) ∧
              (∀ i, |BanditAlgorithm.trajEmpiricalMean i n ω - μvec i| ≤ ξ)))
      ∧ ∫⁻ ω, ((sInf {N : ℕ | ∀ n, N ≤ n →
          (0 < n ∧
              (∀ i, |BanditAlgorithm.trajAllocation i n ω - α i| ≤ ξ) ∧
              (∀ i, |BanditAlgorithm.trajEmpiricalMean i n ω - μvec i| ≤ ξ))} : ℕ) : ℝ≥0∞)
        ∂(BanditAlgorithm.banditTrajMeasure
          (BanditAlgorithm.gaussianBandit μvec) pol) ≠ ⊤ := by
  sorry
