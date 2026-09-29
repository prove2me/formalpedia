-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussian_ts_optimal_exact_rank_reciprocal_tail_sum_bound
-- name    : BanditAlgorithm.gaussian_ts_optimal_exact_rank_reciprocal_tail_sum_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T22:59:48.018427+00:00
-- url     : https://prove2.me/theorems/fa3143bd-5ce3-4b92-8cbd-1812e315ca93
-- title:
--   Optimal-arm reciprocal posterior tails along realized ranks
-- statement:
--   Consider an arbitrary adaptive policy on a unit-variance Gaussian bandit, and fix an optimal arm $i_0$. After the first $s$ realized rewards of that arm, let $G_{i_0,s}(\mu_* - \varepsilon)$ be the posterior Gaussian probability of exceeding $\mu_* - \varepsilon$, where $\varepsilon>0$. There is a universal constant $C>0$ such that, for every horizon $n\ge2$,
--
--   $$
--   \mathbb E\!\left[\sum_{s<T_{i_0}(n)}\left(\frac{1}{G_{i_0,s}(\mu_* - \varepsilon)}-1\right)_+\right]
--   \le C\left(1+\frac{\log n}{\varepsilon^2}\right).
--   $$
--
--   The sum stops at the realized pull count, so each posterior is based on exactly $s$ observed rewards. This is the finite-horizon, exact-rank form of the optimal-arm estimate used in the Gaussian Thompson-sampling analysis.
--
--   **Formalization Note** The expectation is a `lintegral`, and the positive part is encoded by `ENNReal.ofReal`.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Exercise 36.6(a) and its Gaussian-tail hint, printed p. 475 / PDF p. 484; reward-stack convention and Theorem 36.2, printed pp. 463–465 / PDF pp. 472–474. The finite-horizon statement truncates the source sum at the realized pull count and uses the corresponding finite logarithmic envelope.

import Definitions.Def_ThompsonSampling
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm

/-- The optimal-arm reciprocal-posterior-tail estimate from Exercise 36.6(a),
truncated at the realized pull count and at the finite horizon. -/
theorem gaussian_ts_optimal_exact_rank_reciprocal_tail_sum_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k),
        ∀ (i₀ : Fin k),
          banditArmMean (gaussianBandit μvec) i₀ =
            banditOptimalMean (gaussianBandit μvec) →
        ∀ ε : ℝ, 0 < ε →
        ∀ n : ℕ, 2 ≤ n →
          (∫⁻ h, ∑ s ∈ Finset.range (armPullCount i₀ h),
              ENNReal.ofReal
                (1 / gaussianTSTailProb i₀ s
                  (banditArmMean (gaussianBandit μvec) i₀ - ε) h - 1)
              ∂banditMeasure (gaussianBandit μvec) π n) ≤
            ENNReal.ofReal (C * (1 + Real.log n / ε ^ 2)) := by
  sorry

end BanditAlgorithm
