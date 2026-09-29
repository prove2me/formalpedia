-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_hard_tradeoff_analytic
-- name    : BanditAlgorithm.partial_monitoring_hard_tradeoff_analytic
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T17:01:58.710436+00:00
-- url     : https://prove2.me/theorems/bd797c07-825e-430f-8c47-a93c6c3c469a
-- title:
--   Hard-game information–regret tradeoff optimization
-- statement:
--   Let $\varepsilon,\delta>0$ and $C\ge0$. Then there is a constant $c>0$, depending only on these three parameters, such that for every integer $n\ge1$ and every $x\ge0$,
--
--   $$
--   \frac{\varepsilon x}{2}+\frac{n\Delta_n}{8}\exp(-C\Delta_n^2x)\ge c\,n^{2/3},
--   \qquad \Delta_n=\delta n^{-1/3}.
--   $$
--
--   This is the elementary optimization that completes the hard partial-monitoring lower bound after the information/regret tradeoff has been established: either the exploration count $x$ is already of order $n^{2/3}$, or the testing term remains a constant fraction of $n\Delta_n$.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms, Chapter 37, Theorem 37.12 proof, printed p. 491, final display and Exercise 37.7.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

theorem BanditAlgorithm.partial_monitoring_hard_tradeoff_analytic
    (ε C δ : ℝ) (hε : 0 < ε) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ), 1 ≤ n → ∀ x : ℝ, 0 ≤ x →
      ε / 2 * x +
          (n : ℝ) * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) / 8 *
            Real.exp (-C * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 * x) ≥
        c * (n : ℝ) ^ ((2 : ℝ) / 3) := by sorry
