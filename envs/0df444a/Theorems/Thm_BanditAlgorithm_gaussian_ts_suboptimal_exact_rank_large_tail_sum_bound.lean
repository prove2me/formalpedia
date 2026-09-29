-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussian_ts_suboptimal_exact_rank_large_tail_sum_bound
-- name    : BanditAlgorithm.gaussian_ts_suboptimal_exact_rank_large_tail_sum_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T23:00:08.912846+00:00
-- url     : https://prove2.me/theorems/3be909f4-2533-4554-9235-bcbc89cd470a
-- title:
--   Suboptimal-arm large posterior tails along realized ranks
-- statement:
--   Consider an arbitrary adaptive policy on a unit-variance Gaussian bandit. Fix an optimal arm $i_0$ and a suboptimal arm $i$ with gap $\Delta_i>0$. After the first $s$ realized rewards of arm $i$, let $G_{i,s}(\mu_* - \Delta_i/2)$ be the posterior Gaussian probability of exceeding the midpoint between the two arm means. There is a universal constant $C>0$ such that, for every $n\ge2$,
--
--   $$
--   \mathbb E\!\left[\sum_{s<T_i(n)}
--   \mathbf 1\!\left\{G_{i,s}(\mu_* - \Delta_i/2)>\frac1n\right\}\right]
--   \le C\left(1+\frac{\log n}{\Delta_i^2}\right).
--   $$
--
--   This finite estimate is the suboptimal-arm Gaussian posterior-tail input in the pull-count analysis. Exact realized ranks ensure that every empirical mean in the sum is computed from observations that actually occurred.
--
--   **Formalization Note** The expectation is represented by a `lintegral` with values in the extended nonnegative reals.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Exercise 36.6(b), printed p. 475 / PDF p. 484; Theorem 36.2 and Eq. (36.3), printed pp. 463–465 / PDF pp. 472–474. This is the finite-horizon exact-rank envelope underlying the displayed asymptotic estimate.

import Definitions.Def_ThompsonSampling
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm

/-- The suboptimal-arm posterior large-tail estimate from Exercise 36.6(b),
truncated at the realized pull count. -/
theorem gaussian_ts_suboptimal_exact_rank_large_tail_sum_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k),
        ∀ (i₀ : Fin k),
          banditArmMean (gaussianBandit μvec) i₀ =
            banditOptimalMean (gaussianBandit μvec) →
        ∀ (i : Fin k), 0 < banditGap (gaussianBandit μvec) i →
        ∀ n : ℕ, 2 ≤ n →
          (∫⁻ h, ∑ s ∈ Finset.range (armPullCount i h),
              (if 1 / (n : ℝ) <
                  gaussianTSTailProb i s
                    (banditArmMean (gaussianBandit μvec) i₀ -
                      banditGap (gaussianBandit μvec) i / 2) h
                then (1 : ℝ≥0∞) else 0)
              ∂banditMeasure (gaussianBandit μvec) π n) ≤
            ENNReal.ofReal
              (C * (1 + Real.log n /
                banditGap (gaussianBandit μvec) i ^ 2)) := by
  sorry

end BanditAlgorithm
