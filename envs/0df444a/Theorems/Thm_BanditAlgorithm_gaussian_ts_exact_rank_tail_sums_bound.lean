-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussian_ts_exact_rank_tail_sums_bound
-- name    : BanditAlgorithm.gaussian_ts_exact_rank_tail_sums_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T22:45:47.310527+00:00
-- url     : https://prove2.me/theorems/c97d2a5d-9da6-440c-8cd4-48c0dfc038b1
-- title:
--   Finite Gaussian posterior-tail bound along realized arm ranks
-- statement:
--   Consider Gaussian Thompson sampling with unit-variance rewards, an optimal arm $i_0$, and a suboptimal arm $i$ of gap $\Delta_i>0$. For each interaction history $h$, let $T_j(n,h)$ be the number of times arm $j$ has actually been pulled by horizon $n$, and let $G_{j,s}(x,h)$ be the posterior probability, after the first $s$ realized rewards of arm $j$, that its sampled mean is at least $x$. Then there is a universal constant $C>0$ such that, for every $n\ge 2$,
--
--   $$
--   1+\mathbb E\!\left[\sum_{s<T_{i_0}(n)}\left(\frac{1}{G_{i_0,s}(\mu_* - \Delta_i/2)}-1\right)_+\right]
--    +\mathbb E\!\left[\sum_{s<T_i(n)}\mathbf 1\!\left\{G_{i,s}(\mu_* - \Delta_i/2)>\frac1n\right\}\right]
--   \le C\left(1+\frac{\log n}{\Delta_i^2}\right).
--   $$
--
--   The sums stop at the exact realized pull counts. Consequently every empirical mean appearing in them is formed from an actually observed initial reward segment; no value assigned to a nonexistent future pull enters the estimate. This is the Gaussian tail input needed by the exact-rank Thompson-sampling pull-count decomposition.
--
--   **Formalization Note** The expectations are encoded as `lintegral`s in $\mathbb R_{\ge0}\cup\{\infty\}$, and the positive part of the reciprocal-tail term is represented by `ENNReal.ofReal`.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Section 36.2, Theorem 36.2 and Eq. (36.3), printed pp. 463–465; Exercise 36.6(a,b), printed p. 475. This theorem is the source-faithful exact-realized-rank version of the two Gaussian tail estimates used in the proof of Theorem 36.3: stopping each sum at the realized pull count only removes nonnegative terms from the reward-stack sums.

import Definitions.Def_ThompsonSampling
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm

/-- Gaussian posterior-tail estimate for the exact realized-rank sums in the
Thompson-sampling pull-count decomposition. -/
theorem gaussian_ts_exact_rank_tail_sums_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k),
        IsGaussianTSPolicy π →
        ∀ (i₀ : Fin k),
          banditArmMean (gaussianBandit μvec) i₀ =
            banditOptimalMean (gaussianBandit μvec) →
        ∀ (i : Fin k), 0 < banditGap (gaussianBandit μvec) i →
        ∀ n : ℕ, 2 ≤ n →
          1 + (∫⁻ h, ∑ s ∈ Finset.range (armPullCount i₀ h),
                ENNReal.ofReal
                  (1 / gaussianTSTailProb i₀ s
                    (banditArmMean (gaussianBandit μvec) i₀ -
                      banditGap (gaussianBandit μvec) i / 2) h - 1)
                ∂banditMeasure (gaussianBandit μvec) π n)
            + ∫⁻ h, ∑ s ∈ Finset.range (armPullCount i h),
                (if 1 / (n : ℝ) <
                    gaussianTSTailProb i s
                      (banditArmMean (gaussianBandit μvec) i₀ -
                        banditGap (gaussianBandit μvec) i / 2) h
                  then (1 : ℝ≥0∞) else 0)
                ∂banditMeasure (gaussianBandit μvec) π n ≤
            ENNReal.ofReal
              (C * (1 + Real.log n /
                banditGap (gaussianBandit μvec) i ^ 2)) := by
  sorry

end BanditAlgorithm
