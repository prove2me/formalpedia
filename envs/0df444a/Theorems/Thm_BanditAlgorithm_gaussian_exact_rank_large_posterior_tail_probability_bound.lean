-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussian_exact_rank_large_posterior_tail_probability_bound
-- name    : BanditAlgorithm.gaussian_exact_rank_large_posterior_tail_probability_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T01:20:00.545768+00:00
-- url     : https://prove2.me/theorems/5f197b3b-9881-4cff-8d6b-f9688796cb48
-- title:
--   Gaussian Thompson sampling: large posterior tail at one exact rank
-- statement:
--   Consider Gaussian Thompson sampling with independent $\mathcal N(\mu_i,1)$ rewards and posterior variance $1/s$ after $s\ge1$ observations of arm $i$. Fix an optimal arm $i_0$, a suboptimal arm $i$ with gap $\Delta_i>0$, a horizon $n\ge2$, and an exact positive rank $s$. On histories where arm $i$ has been pulled more than $s$ times, the probability that its rank-$s$ posterior assigns more than $1/n$ mass above the midpoint $\mu_* - \Delta_i/2$ is at most
--   $$
--   \begin{cases}
--   \exp\!\left[-\dfrac{s\left(\Delta_i/2-\sqrt{2\log(n)/s}\right)^2}{2}\right], & \dfrac{2\log n}{(\Delta_i/2)^2}<s,\\
--   1, & \text{otherwise.}
--   \end{cases}
--   $$
--   The event reduction uses the Gaussian posterior tail bound and the stopped reward-stack concentration inequality for the first $s$ rewards of arm $i$.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Exercise 36.6(b), printed p. 475 / PDF p. 484; reward-stack construction in §4.6, printed p. 65 / PDF p. 74, and Gaussian Thompson-sampling analysis in Theorem 36.2, printed pp. 463–465 / PDF pp. 472–474.

import Definitions.Def_ThompsonSampling
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.gaussian_exact_rank_large_posterior_tail_probability_bound :
    ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditAlgorithm.BanditPolicy k),
      ∀ (i₀ : Fin k),
        BanditAlgorithm.banditArmMean (BanditAlgorithm.gaussianBandit μvec) i₀ =
          BanditAlgorithm.banditOptimalMean (BanditAlgorithm.gaussianBandit μvec) →
      ∀ (i : Fin k), 0 < BanditAlgorithm.banditGap (BanditAlgorithm.gaussianBandit μvec) i →
      ∀ n : ℕ, 2 ≤ n →
      ∀ s : ℕ, 0 < s →
        (BanditAlgorithm.banditMeasure (BanditAlgorithm.gaussianBandit μvec) π n).real
          {h : BanditAlgorithm.BanditHistory k n |
            s < BanditAlgorithm.armPullCount i h ∧
              1 / (n : ℝ) <
                BanditAlgorithm.gaussianTSTailProb i s
                  (BanditAlgorithm.banditArmMean (BanditAlgorithm.gaussianBandit μvec) i₀ -
                    BanditAlgorithm.banditGap (BanditAlgorithm.gaussianBandit μvec) i / 2) h} ≤
          if 2 * Real.log n /
                (BanditAlgorithm.banditGap (BanditAlgorithm.gaussianBandit μvec) i / 2) ^ 2 < (s : ℝ)
          then
            Real.exp
              (-((s : ℝ) *
                (BanditAlgorithm.banditGap (BanditAlgorithm.gaussianBandit μvec) i / 2 -
                  Real.sqrt (2 * Real.log n / s))) ^ 2 /
                ((2 : ℝ) * (s : ℝ) * 1))
          else 1 := by sorry
