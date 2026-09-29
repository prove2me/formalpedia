-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussian_exact_rank_reciprocal_tail_exponential_bound
-- name    : BanditAlgorithm.gaussian_exact_rank_reciprocal_tail_exponential_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T01:56:32.238835+00:00
-- url     : https://prove2.me/theorems/d753672a-fa0a-49f7-a04d-0d3b14f6df10
-- title:
--   Exponentially decaying exact-rank reciprocal Gaussian tail
-- statement:
--   There is a universal constant $C>0$ such that, for any arm, positive exact realized rank $s$, offset $\varepsilon>0$, policy, and horizon, the expected reciprocal Gaussian posterior-tail term is at most
--   $$
--   2e^{-s\varepsilon^2/8}+\frac{2C}{s\varepsilon^2}e^{-3s\varepsilon^2/32}.
--   $$
--   The expectation includes the indicator that rank $s$ was actually realized. This exponentially decaying refinement is summable over $s$ and is the finite-rank analytic core of Exercise 36.6(a).
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Exercise 36.6(a) and its Gaussian Mills-ratio hint, printed p. 475 / PDF p. 484; reward-stack construction in §4.6, printed p. 65 / PDF p. 74.

import Definitions.Def_ThompsonSampling
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.gaussian_exact_rank_reciprocal_tail_exponential_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditAlgorithm.BanditPolicy k),
        ∀ (i : Fin k) (s : ℕ), 0 < s →
        ∀ ε : ℝ, 0 < ε →
        ∀ n : ℕ,
          (∫⁻ h,
              if s < BanditAlgorithm.armPullCount i h then
                ENNReal.ofReal
                  (1 / BanditAlgorithm.gaussianTSTailProb i s
                    (BanditAlgorithm.banditArmMean (BanditAlgorithm.gaussianBandit μvec) i - ε) h - 1)
              else 0
              ∂BanditAlgorithm.banditMeasure (BanditAlgorithm.gaussianBandit μvec) π n) ≤
            ENNReal.ofReal
              (2 * Real.exp (-((s : ℝ) * ε ^ 2) / 8) +
                2 * C / ((s : ℝ) * ε ^ 2) *
                  Real.exp (-(3 * (s : ℝ) * ε ^ 2) / 32)) := by sorry
