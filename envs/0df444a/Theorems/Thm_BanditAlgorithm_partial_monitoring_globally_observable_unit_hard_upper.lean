-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_globally_observable_unit_hard_upper
-- name    : BanditAlgorithm.partial_monitoring_globally_observable_unit_hard_upper
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T20:19:58.052515+00:00
-- url     : https://prove2.me/theorems/d024f7de-e43d-495c-90f7-e965a5d5d510
-- title:
--   Globally observable unit-loss games have $O(n^{2/3})$ minimax regret
-- statement:
--   For a finite partial-monitoring game whose losses lie in $[0,1]$, assume there are at least two actions and at least one outcome. If every loss-difference vector is globally observable, then there is a constant $C>0$ such that, for every horizon $n\ge 1$, the minimax regret is at most $C n^{2/3}$.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms, Cambridge University Press (2020), Chapter 37: Lemma 37.7 (p. 484), estimator identity (37.3) (p. 486), and proof of Theorem 37.16 (pp. 497–498). https://tor-lattimore.com/downloads/book/book.pdf

import Theorems.Thm_BanditAlgorithm_partial_monitoring_globally_observable_bounded_vector_estimator
import Theorems.Thm_BanditAlgorithm_partial_monitoring_algorithm26_master_bound
import Theorems.Thm_BanditAlgorithm_pmPsi_le_quadratic
import Theorems.Thm_BanditAlgorithm_pmMinimaxRegret_le_policy_of_unit_losses
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BanditAlgorithm

theorem partial_monitoring_globally_observable_unit_hard_upper
    {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊] [MeasurableSingletonClass 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k) (hd : 0 < d)
    (hL : ∀ a i, G.L a i ∈ Set.Icc (0 : ℝ) 1)
    (hglo : GloballyObservable G) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      pmMinimaxRegret G n ≤ C * (n : ℝ) ^ ((2 : ℝ) / 3) := by sorry
