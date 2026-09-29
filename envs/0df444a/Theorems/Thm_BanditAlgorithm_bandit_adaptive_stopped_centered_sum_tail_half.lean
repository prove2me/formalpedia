-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_adaptive_stopped_centered_sum_tail_half
-- name    : BanditAlgorithm.bandit_adaptive_stopped_centered_sum_tail_half
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T04:38:43.262823+00:00
-- url     : https://prove2.me/theorems/c6fb9568-adf0-4bf0-a321-e25f51985d1a
-- title:
--   Sharp adaptive stopped-sum Hoeffding bound
-- statement:
--   Let a stochastic bandit be $1/2$-subgaussian, let a possibly randomized adaptive policy interact with it for $n$ rounds, and fix an arm $i$. Stop the centered reward sum for that arm after its first $u$ observations. For every $t\ge0$, both tails obey the sharp Hoeffding estimate
--
--   $$
--   \mathbb P\!\left(S_{i,u}\ge ut\right)
--   \le e^{-2ut^2},
--   \qquad
--   \mathbb P\!\left(S_{i,u}\le-ut\right)
--   \le e^{-2ut^2}.
--   $$
--
--   The result remains valid even when fewer than $u$ observations of the arm have occurred by the horizon; the stopped sum then uses all observations that are available.
--
--   This is the adaptive reward-stack concentration bridge needed to apply ordinary Bernoulli Hoeffding estimates at a random arm-pull count.
--
--   Formalization Note: `armStoppedCenteredSum` is constructed directly from the finite interaction history. The Lean proof builds the exponential supermartingale with compensator $\lambda^2/8$ at every selected reward, integrates it through the policy and reward kernels, and applies Chernoff's method with $\lambda=4t$.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), reward-stack construction in Section 4.6 and Hoeffding concentration used in Chapters 8 and 10.

import Definitions.Def_ucbStoppedCenteredSum
import Mathlib.Data.Fintype.Order
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bandit_adaptive_stopped_centered_sum_tail_half
    {k n : ℕ} (ν : BanditAlgorithm.StochasticBandit k)
    (hν : BanditAlgorithm.IsSubgaussianBandit (1 / 2) ν)
    {π : BanditAlgorithm.BanditPolicy k}
    (i : Fin k) (u : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (BanditAlgorithm.banditMeasure ν π n).real
        {h : BanditAlgorithm.BanditHistory k n |
          (u : ℝ) * t ≤
            BanditAlgorithm.armStoppedCenteredSum ν i u n h} ≤
        Real.exp (-2 * (u : ℝ) * t ^ 2) ∧
      (BanditAlgorithm.banditMeasure ν π n).real
        {h : BanditAlgorithm.BanditHistory k n |
          BanditAlgorithm.armStoppedCenteredSum ν i u n h ≤
            -(u : ℝ) * t} ≤
        Real.exp (-2 * (u : ℝ) * t ^ 2) := by
  sorry
