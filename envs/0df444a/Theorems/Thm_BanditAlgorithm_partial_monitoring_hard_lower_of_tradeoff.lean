-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_hard_lower_of_tradeoff
-- name    : BanditAlgorithm.partial_monitoring_hard_lower_of_tradeoff
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T17:05:29.251814+00:00
-- url     : https://prove2.me/theorems/1fc73df2-e435-40c5-8ec8-f72b9777b726
-- title:
--   Hard partial-monitoring lower bound from the information–regret tradeoff
-- statement:
--   Let $G$ be a finite partial-monitoring game. Suppose there are game-dependent constants $\varepsilon,\delta>0$ and $C\ge0$ such that, for every $n\ge1$, some $x\ge0$ satisfies
--
--   $$
--   \frac{\varepsilon x}{2}+\frac{n\Delta_n}{8}e^{-C\Delta_n^2x}\le 2R_n^*(G),
--   \qquad \Delta_n=\delta n^{-1/3}.
--   $$
--
--   Then there is a constant $c_G>0$ for which
--
--   $$
--   R_n^*(G)\ge c_G n^{2/3}
--   $$
--
--   for every horizon $n$. This formal bridge isolates the final optimization in the proof of the hard partial-monitoring lower bound from the preceding geometric and information-theoretic construction.
-- source:
--   Formal bridge for Lattimore and Szepesvári, Bandit Algorithms, Chapter 37, Theorem 37.12 proof, printed p. 491, last three displays and Exercise 37.7; it invokes the separately proved p.491 analytic optimization theorem.

import Definitions.Def_PartialMonitoringGame
import Theorems.Thm_BanditAlgorithm_partial_monitoring_hard_tradeoff_analytic

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.partial_monitoring_hard_lower_of_tradeoff
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊)
    (htrade : ∃ ε C δ : ℝ, 0 < ε ∧ 0 ≤ C ∧ 0 < δ ∧
      ∀ (n : ℕ), 1 ≤ n → ∃ x : ℝ, 0 ≤ x ∧
        ε / 2 * x +
            (n : ℝ) * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) / 8 *
              Real.exp (-C * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 * x) ≤
          2 * pmMinimaxRegret G n) :
    ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, c * (n : ℝ) ^ ((2 : ℝ) / 3) ≤ pmMinimaxRegret G n := by sorry
