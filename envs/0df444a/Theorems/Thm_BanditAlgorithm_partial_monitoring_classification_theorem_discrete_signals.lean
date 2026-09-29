-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_classification_theorem_discrete_signals
-- name    : BanditAlgorithm.partial_monitoring_classification_theorem_discrete_signals
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T03:56:16.930504+00:00
-- url     : https://prove2.me/theorems/84cd9510-5ac6-40cf-a29f-aeb812b88442
-- title:
--   Theorem 37.11: classification of finite partial-monitoring games (discrete signals)
-- statement:
--   Let $G=(L,\Phi)$ be a finite adversarial partial-monitoring game with $k$ actions, $d$ outcomes, and a finite signal alphabet $\mathcal S$ equipped with the discrete measurable structure. Write $R_n^*(G)$ for its minimax regret at horizon $n$. Then
--
--   $$
--   R_n^*(G)=
--   \begin{cases}
--   0, & \text{if }G\text{ has no neighbouring actions},\\
--   \Theta(\sqrt n), & \text{if }G\text{ is locally observable and has neighbouring actions},\\
--   \Theta(n^{2/3}), & \text{if }G\text{ is globally observable but not locally observable},\\
--   \Omega(n), & \text{if }G\text{ has neighbouring actions but is not globally observable}.
--   \end{cases}
--   $$
--
--   The constants implicit in $\Theta$ and $\Omega$, as well as the horizon from which the bounds hold, may depend on the game. This classification separates trivial, easy, hard, and hopeless finite partial-monitoring games according to the geometry of their cells and the observability of neighbouring loss differences.
--
--   **Formalization Note** The hypothesis that every singleton of $\mathcal S$ is measurable, together with finiteness of $\mathcal S$, makes its measurable structure discrete. This is the measurable-space counterpart of the source treating the finite signal alphabet as an ordinary discrete set.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Chapter 37, finite signal alphabet on p. 480 and Theorem 37.11 on p. 487, Cambridge University Press, 2020.

import Definitions.Def_PartialMonitoringGame
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.partial_monitoring_classification_theorem_discrete_signals
    {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊] [MeasurableSingletonClass 𝕊]
    (G : PartialMonitoringGame k d 𝕊) :
    (¬ HasNeighbouringActions G → ∀ n : ℕ, pmMinimaxRegret G n = 0) ∧
    (LocallyObservable G ∧ HasNeighbouringActions G →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        c * Real.sqrt n ≤ pmMinimaxRegret G n ∧
        pmMinimaxRegret G n ≤ C * Real.sqrt n) ∧
    (GloballyObservable G ∧ ¬ LocallyObservable G →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        c * (n : ℝ) ^ ((2 : ℝ) / 3) ≤ pmMinimaxRegret G n ∧
        pmMinimaxRegret G n ≤ C * (n : ℝ) ^ ((2 : ℝ) / 3)) ∧
    (HasNeighbouringActions G ∧ ¬ GloballyObservable G →
      ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        c * (n : ℝ) ≤ pmMinimaxRegret G n) := by
  sorry
