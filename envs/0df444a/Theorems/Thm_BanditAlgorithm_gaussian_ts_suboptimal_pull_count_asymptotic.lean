-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussian_ts_suboptimal_pull_count_asymptotic
-- name    : BanditAlgorithm.gaussian_ts_suboptimal_pull_count_asymptotic
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T22:19:53.473932+00:00
-- url     : https://prove2.me/theorems/f1f992c1-f237-4873-806c-76233668e54b
-- title:
--   Asymptotic pull count of a suboptimal arm under Gaussian TS
-- statement:
--   Let Thompson sampling use independent Gaussian posterior perturbations of variance $1/T_i(t)$ in a unit-variance Gaussian $k$-armed bandit. For any suboptimal arm $i$ with gap $\Delta_i>0$, its expected number of pulls satisfies
--
--   $$
--   \lim_{n\to\infty}\frac{\mathbb E[T_i(n)]}{\log n}=\frac{2}{\Delta_i^2}.
--   $$
--
--   This is the armwise probabilistic core of the instance-dependent asymptotic regret theorem. Summing it against the gaps via the regret decomposition yields the Lai--Robbins-optimal coefficient $\sum_{i:\Delta_i>0}2/\Delta_i$.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Theorem 36.3 and its proof, printed pp. 464-468, using Theorem 36.2.

import Definitions.Def_ThompsonSampling
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory Filter

theorem BanditAlgorithm.gaussian_ts_suboptimal_pull_count_asymptotic
    {k : ℕ} [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k)
    (hπ : IsGaussianTSPolicy π) (i : Fin k)
    (hi : 0 < banditGap (gaussianBandit μvec) i) :
    Tendsto
      (fun n : ℕ ↦
        (∫ h, (armPullCount i h : ℝ)
          ∂banditMeasure (gaussianBandit μvec) π n) / Real.log n)
      atTop
      (nhds (2 / banditGap (gaussianBandit μvec) i ^ 2)) := by
  sorry
