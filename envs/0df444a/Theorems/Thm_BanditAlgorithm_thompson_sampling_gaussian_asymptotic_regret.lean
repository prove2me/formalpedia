-- Prove2me | Theorems.Thm_BanditAlgorithm_thompson_sampling_gaussian_asymptotic_regret
-- name    : BanditAlgorithm.thompson_sampling_gaussian_asymptotic_regret
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T19:52:47.881483+00:00
-- url     : https://prove2.me/theorems/d71b4dde-fe5a-4027-a187-94e94dc4eebe
-- title:
--   Gaussian Thompson Sampling has asymptotically optimal logarithmic regret
-- statement:
--   Consider Thompson sampling with the Gaussian update rule of Algorithm 24 on a $k$-armed unit-variance Gaussian bandit with mean vector $\mu$. Let $\Delta_i=\mu^*-\mu_i$ be the gap of arm $i$, and let $R_n$ denote expected cumulative regret. Then
--
--   $$
--   \lim_{n\to\infty}\frac{R_n}{\log n}
--   =
--   \sum_{i:\Delta_i>0}\frac{2}{\Delta_i}.
--   $$
--
--   Thus Gaussian Thompson sampling attains the Lai–Robbins instance-dependent asymptotic constant, with a genuine limit rather than only a limsup. The statement allows arbitrary real means because translating all Gaussian means does not change the gaps or the algorithm's regret.
--
--   **Formalization Note** The policy is characterized extensionally by `IsGaussianTSPolicy`, including the forced initial pulls induced by the point mass at positive infinity.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Theorem 36.3, Eq. (36.6), printed p. 465; based on the pull-count decomposition in Theorem 36.2, printed p. 463.

import Definitions.Def_ThompsonSampling
import Definitions.Def_GaussianBandit
import Definitions.Def_banditRegret

open MeasureTheory ProbabilityTheory Filter

theorem BanditAlgorithm.thompson_sampling_gaussian_asymptotic_regret :
    ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k),
      IsGaussianTSPolicy π →
      Tendsto (fun n : ℕ ↦ banditRegret (gaussianBandit μvec) π n / Real.log n)
        atTop
        (nhds (∑ i ∈ Finset.univ.filter
            (fun i ↦ 0 < banditGap (gaussianBandit μvec) i),
          2 / banditGap (gaussianBandit μvec) i)) := by
  sorry
