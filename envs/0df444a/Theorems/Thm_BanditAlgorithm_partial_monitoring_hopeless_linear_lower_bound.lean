-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_hopeless_linear_lower_bound
-- name    : BanditAlgorithm.partial_monitoring_hopeless_linear_lower_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T15:36:37.802136+00:00
-- url     : https://prove2.me/theorems/694293a7-0e6e-4214-8692-56bef76db291
-- title:
--   Theorem 37.13: $\Omega(n)$ lower bound for hopeless games
-- statement:
--   Let $G=(L,\Phi)$ be a finite partial-monitoring game with a finite discrete signal alphabet. Suppose that $G$ has neighbouring actions but is not globally observable. Then there are a game-dependent constant $c_G>0$ and a horizon $N_G$ such that
--
--   $$
--   c_G n \le R_n^*(G) \qquad \text{for every }n\ge N_G.
--   $$
--
--   This is the hopeless branch of the classification. Non-global observability gives two stochastic environments that induce identical feedback laws for every policy while favouring different neighbouring actions, forcing linear regret.
--
--   **Formalization Note** A neighbouring pair supplies the source theorem’s requirement of at least two non-dominated actions.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Chapter 37, Section 37.4, Theorem 37.13 and proof sketch, printed pp. 491–492 (PDF pp. 499–500), https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.partial_monitoring_hopeless_linear_lower_bound
    {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊] [MeasurableSingletonClass 𝕊]
    (G : PartialMonitoringGame k d 𝕊)
    (h : HasNeighbouringActions G ∧ ¬ GloballyObservable G) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * (n : ℝ) ≤ pmMinimaxRegret G n := by
  sorry
