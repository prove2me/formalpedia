-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_hard_game_tradeoff
-- name    : BanditAlgorithm.partial_monitoring_hard_game_tradeoff
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T17:06:57.601652+00:00
-- url     : https://prove2.me/theorems/663eefec-0cac-4a49-a041-eeeb30aa4d11
-- title:
--   Hard-game geometric and information–regret tradeoff
-- statement:
--   Let $G$ be a finite globally observable but not locally observable partial-monitoring game. Then there are game-dependent constants $\varepsilon,\delta>0$ and $C\ge0$ such that for every horizon $n\ge1$ there is an expected off-neighbourhood play count $x\ge0$ satisfying
--
--   $$
--   \frac{\varepsilon x}{2}+\frac{n\Delta_n}{8}\exp(-C\Delta_n^2x)\le 2R_n^*(G),
--   \qquad \Delta_n=\delta n^{-1/3}.
--   $$
--
--   The first term is the regret paid for informative actions outside the critical neighbourhood; the second is the testing cost for distinguishing the two stochastic environments constructed around a non-locally-observable neighbouring pair. This is precisely the geometric and information-theoretic core of the hard-game lower bound.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms, Chapter 37, Theorem 37.12 proof, printed pp. 488–491: Step 1 and Eq. (37.5)–(37.7), Step 2 Eq. (37.8)–(37.9), Step 3 Eq. (37.10) and the Bretagnolle–Huber display.

import Definitions.Def_PartialMonitoringGame
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.partial_monitoring_hard_game_tradeoff {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊] (G : PartialMonitoringGame k d 𝕊)
    (hglob : GloballyObservable G) (hloc : ¬ LocallyObservable G) :
    ∃ ε C δ : ℝ, 0 < ε ∧ 0 ≤ C ∧ 0 < δ ∧
      ∀ (n : ℕ), 1 ≤ n → ∃ x : ℝ, 0 ≤ x ∧
        ε / 2 * x +
            (n : ℝ) * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) / 8 *
              Real.exp (-C * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 * x) ≤
          2 * pmMinimaxRegret G n := by sorry
