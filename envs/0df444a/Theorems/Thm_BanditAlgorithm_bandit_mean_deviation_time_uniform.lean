-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_mean_deviation_time_uniform
-- name    : BanditAlgorithm.bandit_mean_deviation_time_uniform
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-01T16:19:30.961206+00:00
-- url     : https://prove2.me/theorems/ea877ca5-9914-4616-8d97-948776074345
-- title:
--   Time-uniform deviation bound for a bandit's empirical means
-- statement:
--   For every arm $a$ and every $\delta\in(0,1]$, under any sampling rule,
--   $$\mathbb P\Big(\exists n:\ T_a(n)\ge 1\ \text{ and }\ (\hat\mu_a(n)-\mu_a)^2>\frac{4\big(\log(1/\delta)+\tfrac12\log(1+T_a(n))\big)}{T_a(n)}\Big)\ \le\ \delta .$$
--
--   Equivalently, with probability at least $1-\delta$ the empirical mean of arm $a$ is within $2\sqrt{(\log(1/\delta)+\tfrac12\log(1+T_a(n)))/T_a(n)}$ of the truth at *every* round at which the arm has been played.
--
--   Uniformity in the round is the point. The number of pulls $T_a(n)$ is itself random and adapted, so a fixed-sample Chernoff bound cannot simply be evaluated at it, and a union bound over rounds costs a factor growing with the horizon. The route is the method of mixtures: average the exponential martingales $\exp(\lambda S_a(n)-\lambda^2T_a(n)/2)$ over a Gaussian prior on the tilt $\lambda$, giving a nonnegative supermartingale in closed form, and apply Ville's maximal inequality to it. The price of the mixture is exactly the $\tfrac12\log(1+T_a(n))$ term.
-- source:
--   Method of mixtures: Robbins & Siegmund 1970; de la Pena, Klass & Lai, Ann. Probab. 32 (2004); Kaufmann & Koolen, JMLR 22 (2021). Used for the empirical-mean half of Proposition 13 in Garivier & Kaufmann, COLT 2016.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem BanditAlgorithm.bandit_mean_deviation_time_uniform {k : ℕ} [NeZero k]
    (μvec : Fin k → ℝ) (pol : BanditAlgorithm.BanditPolicy k) (a : Fin k) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ | ∃ n : ℕ, 1 ≤ BanditAlgorithm.trajPullCount a n ω ∧
          4 * (Real.log (1 / δ)
              + Real.log (1 + (BanditAlgorithm.trajPullCount a n ω : ℝ)) / 2)
              / (BanditAlgorithm.trajPullCount a n ω : ℝ)
            < (BanditAlgorithm.trajEmpiricalMean a n ω - μvec a) ^ 2}
      ≤ ENNReal.ofReal δ := by
  sorry
