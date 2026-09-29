-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_easy_sqrt_lower_bound
-- name    : BanditAlgorithm.partial_monitoring_easy_sqrt_lower_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T15:36:23.35226+00:00
-- url     : https://prove2.me/theorems/b716c8b8-62a9-4ae6-918a-9183619d19b3
-- title:
--   Theorem 37.14: $\Omega(\sqrt n)$ lower bound for easy games
-- statement:
--   Let $G=(L,\Phi)$ be a finite locally observable partial-monitoring game with a finite discrete signal alphabet and at least one pair of neighbouring actions. Then there are a game-dependent constant $c_G>0$ and a horizon $N_G$ such that
--
--   $$
--   c_G\sqrt n \le R_n^*(G) \qquad \text{for every }n\ge N_G.
--   $$
--
--   This is the lower half of the easy-game $\Theta(\sqrt n)$ classification. It is obtained by testing two nearby stochastic environments on opposite sides of a neighbouring cell boundary.
--
--   **Formalization Note** The source says “for all large enough $n$”; the existential threshold $N_G$ makes that quantifier explicit.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Chapter 37, Section 37.4, Theorem 37.14 and proof sketch, printed p. 492 (PDF p. 500), https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame
import Mathlib.Data.Real.Sqrt

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.partial_monitoring_easy_sqrt_lower_bound
    {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊] [MeasurableSingletonClass 𝕊]
    (G : PartialMonitoringGame k d 𝕊)
    (h : LocallyObservable G ∧ HasNeighbouringActions G) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * Real.sqrt n ≤ pmMinimaxRegret G n := by
  sorry
