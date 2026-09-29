-- Prove2me | Theorems.Thm_BanditAlgorithm_standardGaussian_mills_lower_bound
-- name    : BanditAlgorithm.standardGaussian_mills_lower_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T23:28:45.346247+00:00
-- url     : https://prove2.me/theorems/c927f23a-f026-4b73-8a04-62bb56807870
-- title:
--   Coarse lower Mills bound for the standard Gaussian tail
-- statement:
--   There is a universal constant $c>0$ such that the upper tail of a standard Gaussian satisfies, for every $u\ge0$,
--
--   $$
--   \mathbb P\{Z>u\}\ge \frac{c}{u+1}\exp\!\left(-\frac{u^2}{2}\right),
--   \qquad Z\sim\mathcal N(0,1).
--   $$
--
--   This coarse lower Mills bound is obtained by integrating the Gaussian density over the short interval $(u,u+1/(u+1)]$.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Gaussian-tail hint to Exercise 36.6, printed p. 475 / PDF p. 484: the displayed lower bound on the standard normal upper tail.

import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- A coarse Mills-ratio lower bound sufficient for Thompson sampling. -/
theorem standardGaussian_mills_lower_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ u : ℝ, 0 ≤ u →
        c / (u + 1) * Real.exp (-u ^ 2 / 2) ≤
          (gaussianReal 0 1).real (Set.Ioi u) := by
  sorry

end BanditAlgorithm
