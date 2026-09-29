-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_asymptotically_optimal_ucb_regret_bound
-- name    : BanditAlgorithm.bandit_asymptotically_optimal_ucb_regret_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-19T02:57:41.815016+00:00
-- url     : https://prove2.me/theorems/3feec2a8-e346-4871-a376-a4225a37431d
-- statement:
--   (Asymptotically optimal UCB, finite-time, GOAL) For any 1-subgaussian $k$-armed bandit $\nu$ and any policy $\pi$ that is an instance of Algorithm 6 (index $\hat\mu_i(t-1) + \sqrt{\frac{2\log f(t)}{T_i(t-1)}}$ with $f(t) = 1 + t\log^2 t$), the regret satisfies
--
--   $$R_n \le \sum_{i:\Delta_i>0} \inf_{\varepsilon\in(0,\Delta_i)} \Delta_i\left(1 + \frac{5}{\varepsilon^2} + \frac{2\big(\log f(n) + \sqrt{\pi\log f(n)} + 1\big)}{(\Delta_i-\varepsilon)^2}\right).$$
--
--   The per-arm infimum inside the sum is encoded in the equivalent $\forall$-family form: the bound holds at every family $\varepsilon : \mathrm{Fin}\ k \to \mathbb{R}$ with $\varepsilon_i \in (0, \Delta_i)$ for each suboptimal arm $i$.
-- source:
--   L&S Theorem 8.1, Eq. (8.1), p.117

import Definitions.Def_banditRegret
import Definitions.Def_asymptoticUcbPolicy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bandit_asymptotically_optimal_ucb_regret_bound {k : ℕ}
    {ν : StochasticBandit k} (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} (hπ : IsAsymptoticUCBPolicy π) (n : ℕ)
    (ε : Fin k → ℝ)
    (hε : ∀ i, 0 < banditGap ν i → ε i ∈ Set.Ioo 0 (banditGap ν i)) :
    banditRegret ν π n ≤
      ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < banditGap ν i),
        banditGap ν i *
          (1 + 5 / ε i ^ 2 +
            2 * (Real.log (asymptoticUcbSchedule n) +
                Real.sqrt (Real.pi * Real.log (asymptoticUcbSchedule n)) + 1) /
              (banditGap ν i - ε i) ^ 2) := by
  sorry
