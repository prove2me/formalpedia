-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_trivial_zero_regret
-- name    : BanditAlgorithm.partial_monitoring_trivial_zero_regret
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T15:36:18.800085+00:00
-- url     : https://prove2.me/theorems/611a0e82-3578-4583-929d-9c8279ec03b5
-- title:
--   Theorem 37.22: zero regret without neighbouring actions
-- statement:
--   Let $G=(L,\Phi)$ be a finite adversarial partial-monitoring game with a finite discrete signal alphabet. If $G$ has no pair of neighbouring actions, then its minimax regret vanishes at every horizon:
--
--   $$
--   R_n^*(G)=0 \qquad \text{for every }n\ge 0.
--   $$
--
--   This is the trivial branch of the classification theorem. Geometrically, the absence of neighbouring cells forces one action to be optimal throughout the outcome simplex, so the constant policy playing that action incurs no regret.
--
--   **Formalization Note** The discrete-signal instance matches the finite signal alphabet in the source and makes arbitrary history-dependent policies measurable.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Chapter 37, Section 37.8, Theorem 37.22 and its proof, printed p. 503 (PDF p. 511), https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.partial_monitoring_trivial_zero_regret
    {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊] [MeasurableSingletonClass 𝕊]
    (G : PartialMonitoringGame k d 𝕊)
    (h : ¬ HasNeighbouringActions G) :
    ∀ n : ℕ, pmMinimaxRegret G n = 0 := by
  sorry
