-- Prove2me | Theorems.Thm_BanditAlgorithm_asymptotic_ucb_suboptimal_arm_expected_pull_count_bound
-- name    : BanditAlgorithm.asymptotic_ucb_suboptimal_arm_expected_pull_count_bound
-- status  : Proved
-- author  : @allychan327
-- created : 2026-07-21T02:26:07.814948+00:00
-- url     : https://prove2.me/theorems/a2c53ad6-8863-41cb-b9df-e648ebb6cc11
-- title:
--   Algorithm 6 per-arm expected pull-count bound
-- statement:
--   Let $\nu$ be a finite-armed stochastic bandit whose reward laws are 1-subgaussian, and let $\pi$ be Algorithm 6 with index $\widehat\mu_i(t-1)+\sqrt{2\log f(t)/T_i(t-1)}$, where $f(t)=1+t\log^2 t$. Fix a suboptimal arm $i$ with gap $\Delta_i>0$, a horizon $n$, and $0<\varepsilon<\Delta_i$. Then\n\n$$\mathbb E_{\nu,\pi}[T_i(n)] \le 1+\frac{5}{\varepsilon^2}+\frac{2}{(\Delta_i-\varepsilon)^2}\left(\log f(n)+\sqrt{\pi\log f(n)}+1\right).$$\n\nThis per-arm occupation estimate is the reusable probabilistic core of the finite-time regret bound in Theorem 8.1, before multiplying by $\Delta_i$ and summing over suboptimal arms.\n\n**Formalization Note** The expectation is represented as the integral of the arm pull count against the canonical bandit-history measure.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Chapter 8, proof of Theorem 8.1, Eq. (8.4), printed pp. 119-120 / PDF pp. 128-129; the optimal-arm underestimation expectation is bounded by 5/epsilon^2 and the selected suboptimal-arm expectation is bounded using Lemma 8.2 by the displayed logarithmic term on printed p. 120 / PDF p. 129.

import Definitions.Def_banditRegret
import Definitions.Def_asymptoticUcbPolicy

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.asymptotic_ucb_suboptimal_arm_expected_pull_count_bound {k : ℕ}
    {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsAsymptoticUCBPolicy π)
    (n : ℕ) (i : Fin k) (ε : ℝ)
    (hgap : 0 < BanditAlgorithm.banditGap ν i) (hεpos : 0 < ε)
    (hεlt : ε < BanditAlgorithm.banditGap ν i) :
    MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
        (fun h ↦ (BanditAlgorithm.armPullCount i h : ℝ)) ≤
      1 + 5 / ε ^ 2 +
        2 / (BanditAlgorithm.banditGap ν i - ε) ^ 2 *
          (Real.log (BanditAlgorithm.asymptoticUcbSchedule n) +
            Real.sqrt (Real.pi * Real.log (BanditAlgorithm.asymptoticUcbSchedule n)) + 1) := by sorry
