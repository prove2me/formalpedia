-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_adaptive_stopped_centered_sum_tail
-- name    : BanditAlgorithm.bandit_adaptive_stopped_centered_sum_tail
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-28T15:05:25.173531+00:00
-- url     : https://prove2.me/theorems/a5d67397-9516-4b98-bc54-559cc8bb4036
-- statement:
--   Fix an arm $i$ in a $1$-subgaussian stochastic bandit, an arbitrary possibly randomized policy $\pi$, a horizon $n$, and a pull cap $u$. Let
--   $$
--   S_{i,u}(n)=\sum_{s\le n}\mathbf{1}\{A_s=i,\ T_i(s-1)<u\}\,(X_s-\mu_i)
--   $$
--   be the centered reward accumulated only over the first $u$ pulls of arm $i$. For every $t\ge 0$,
--   $$
--   \mathbb{P}_{\nu\pi}\!\left(S_{i,u}(n)\ge ut\right)\le e^{-ut^2/2},
--   \qquad
--   \mathbb{P}_{\nu\pi}\!\left(S_{i,u}(n)\le-ut\right)\le e^{-ut^2/2}.
--   $$
--   This is the canonical-history formulation of the reward-stack and bounded optional-stopping concentration argument.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), reward-stack model in §4.6, printed p. 65 / PDF p. 74, and Exercise 4.4, printed p. 69 / PDF p. 78; the same stopped centered-reward argument is used in Theorem 7.1, Eqs. (7.7)–(7.10), printed pp. 106–108 / PDF pp. 115–117, and in Theorem 8.1, Eq. (8.4), printed pp. 119–120 / PDF pp. 128–129.

import Definitions.Def_ucbStoppedCenteredSum
import Mathlib.Data.Fintype.Order
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bandit_adaptive_stopped_centered_sum_tail
    {k n : ℕ} (ν : BanditAlgorithm.StochasticBandit k)
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {π : BanditAlgorithm.BanditPolicy k}
    (i : Fin k) (u : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (BanditAlgorithm.banditMeasure ν π n).real
        {h : BanditAlgorithm.BanditHistory k n |
          (u : ℝ) * t ≤
            BanditAlgorithm.armStoppedCenteredSum ν i u n h} ≤
        Real.exp (-(u : ℝ) * t ^ 2 / 2) ∧
      (BanditAlgorithm.banditMeasure ν π n).real
        {h : BanditAlgorithm.BanditHistory k n |
          BanditAlgorithm.armStoppedCenteredSum ν i u n h ≤
            -(u : ℝ) * t} ≤
        Real.exp (-(u : ℝ) * t ^ 2 / 2) := by
  sorry
