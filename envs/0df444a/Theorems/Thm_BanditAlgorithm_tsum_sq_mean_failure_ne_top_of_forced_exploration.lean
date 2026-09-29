-- Prove2me | Theorems.Thm_BanditAlgorithm_tsum_sq_mean_failure_ne_top_of_forced_exploration
-- name    : BanditAlgorithm.tsum_sq_mean_failure_ne_top_of_forced_exploration
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-01T16:25:57.277061+00:00
-- url     : https://prove2.me/theorems/3ebf432d-214a-42df-a71e-8f9e3c182548
-- title:
--   Summability of quadratically weighted deviation failures
-- statement:
--   Suppose a sampling rule guarantees, almost surely, that every arm has been played at least $\sqrt t-2k$ times by round $t$. Then for every accuracy $\xi>0$
--   $$\sum_{m\ge 0}(m+1)^2\,\mathbb P\big(\exists i:\ |\hat\mu_i(m)-\mu_i|>\xi\big)<\infty .$$
--
--   The forced-exploration floor makes every empirical mean rest on $\asymp\sqrt m$ samples, so the time-uniform confidence bound gives a per-round failure probability decaying like $e^{-c\xi^2\sqrt m}$, and a sub-exponential decay absorbs any polynomial weight.
--
--   The quadratic weight is what a *delayed* covering argument costs downstream: an allocation failure at round $n$ is covered by mean failures from round $\theta n$ on, and exchanging the two sums turns a linear weight into a quadratic one. So a first moment for the allocation is a second moment for the means.
--
--   The count bound is assumed only almost surely, which is the strongest form any sampling rule delivers: a policy constrains only the trajectories in its support, while the canonical trajectory space contains every sequence of arm-reward pairs. The cost is a single intersection with a full-measure set inside the union bound.
-- source:
--   Empirical-mean half of Proposition 13 in Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, with the quadratic weight needed for the allocation half.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem BanditAlgorithm.tsum_sq_mean_failure_ne_top_of_forced_exploration
    {k : ℕ} [NeZero k] (μvec : Fin k → ℝ)
    (pol : BanditAlgorithm.BanditPolicy k) {ξ : ℝ} (hξ : 0 < ξ)
    (hcount : ∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure
        (BanditAlgorithm.gaussianBandit μvec) pol),
      ∀ (t : ℕ) (j : Fin k),
        Real.sqrt (t : ℝ) - 2 * (k : ℝ) ≤ (BanditAlgorithm.trajPullCount j t ω : ℝ)) :
    ∑' m : ℕ, ((m : ℝ≥0∞) + 1) ^ 2 *
        BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol
          {ω : ℕ → Fin k × ℝ | ∀ i : Fin k,
            |BanditAlgorithm.trajEmpiricalMean i m ω - μvec i| ≤ ξ}ᶜ ≠ ⊤ := by
  sorry
