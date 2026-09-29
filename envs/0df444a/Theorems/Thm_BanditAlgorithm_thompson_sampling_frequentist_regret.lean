-- Prove2me | Theorems.Thm_BanditAlgorithm_thompson_sampling_frequentist_regret
-- name    : BanditAlgorithm.thompson_sampling_frequentist_regret
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-30T15:44:20.91877+00:00
-- url     : https://prove2.me/theorems/a8d19e64-3244-44b7-b1ec-63b3ddae5df8
-- statement:
--   (Thompson sampling frequentist optimality, GOAL; L&S Theorem 36.3) Thompson sampling with $F_i(1) = \delta_\infty$ and Gaussian updates $\mathcal{N}(\hat\mu_i(t), 1/T_i(t))$ (Algorithm 24) on any unit-variance Gaussian bandit $\nu \in \mathcal{E}^k_{\mathcal{N}}(1)$ satisfies
--
--   $$\lim_{n\to\infty} \frac{R_n}{\log n} = \sum_{i:\Delta_i>0} \frac{2}{\Delta_i}$$
--
--   (a genuine limit); and there is a universal constant $C > 0$ such that
--
--   $$R_n \le C\sqrt{kn\log n}$$
--
--   for all $n \ge 2$ and all Gaussian bandits with means in $[0,1]$ (the normalization of Theorem 36.1; as literally stated in the book the distribution-free bound fails for $n = 1$ and for unbounded means, since the forced first pull of each arm costs $\sum_i \Delta_i$).
-- source:
--   L&S Theorem 36.3, p.465

import Definitions.Def_banditRegret
import Definitions.Def_GaussianBandit
import Definitions.Def_ThompsonSampling


open MeasureTheory ProbabilityTheory Filter

theorem BanditAlgorithm.thompson_sampling_frequentist_regret :
    (∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k),
      IsGaussianTSPolicy π →
      Tendsto (fun n : ℕ ↦ banditRegret (gaussianBandit μvec) π n / Real.log n)
        atTop
        (nhds (∑ i ∈ Finset.univ.filter
            (fun i ↦ 0 < banditGap (gaussianBandit μvec) i),
          2 / banditGap (gaussianBandit μvec) i))) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k),
      IsGaussianTSPolicy π → (∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ n : ℕ, 2 ≤ n →
        banditRegret (gaussianBandit μvec) π n ≤
          C * Real.sqrt (k * n * Real.log n)) := by
  sorry
