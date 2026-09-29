-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_linear_lower_of_globally_invisible_alternatives
-- name    : BanditAlgorithm.partial_monitoring_linear_lower_of_globally_invisible_alternatives
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T16:34:35.371996+00:00
-- url     : https://prove2.me/theorems/3a4a47c7-6360-40fc-b75b-bead9de1853e
-- title:
--   Globally invisible alternatives force linear minimax regret
-- statement:
--   Suppose a finite partial-monitoring game admits two symmetric stochastic environments around a neighbouring edge such that every action has exactly the same feedback distribution in the two environments, while one environment favors one endpoint and the other favors the other endpoint by a fixed positive amount. Assume also the usual uniform outside-neighbourhood gap and neighbourhood interpolation identity. Then there is a constant $c>0$ such that, for every horizon $n$,
--
--   $$
--   R_n^*(G) \ge c n.
--   $$
--
--   The result isolates the information-theoretic part of the hopeless-game lower bound: because the two history laws are identical, no policy can learn which endpoint is optimal, so one of the two environments incurs a constant expected loss per round.
--
--   **Formalization Note** The proof uses the stochastic-to-adversarial regret comparison and the Bretagnolle–Huber testing inequality; global feedback invisibility makes the relevant KL divergence exactly zero.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Theorem 37.13 and its reference to the testing argument in Eqs. (37.8)–(37.10), printed pp. 490–492 (PDF pp. 498–500); https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.partial_monitoring_linear_lower_of_globally_invisible_alternatives
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊] [DecidableEq 𝕊]
    (G : PartialMonitoringGame k d 𝕊)
    (hgeom : ∃ a b : Fin k, ∃ u q : Fin d → ℝ, ∃ ε δ : ℝ,
      NeighbouringActions G a b ∧ 0 < ε ∧ 0 < δ ∧
      (∑ i, q i) = 0 ∧
      (∑ i, (G.L a i - G.L b i) * q i) = 1 ∧
      (∀ c : Fin k, ∀ σ : 𝕊,
        ∑ i ∈ Finset.univ.filter (fun i ↦ G.Φ c i = σ), q i = 0) ∧
      ∀ Δ : ℝ, 0 < Δ → Δ ≤ δ →
        let ua := fun i ↦ u i - Δ * q i
        let ub := fun i ↦ u i + Δ * q i
        ua ∈ pmCell G a ∧ ub ∈ pmCell G b ∧
        (∀ c : Fin k, c ∉ pmNeighbourhood G a b →
          ε / 2 ≤ ∑ i, (G.L c i - G.L a i) * ua i ∧
          ε / 2 ≤ ∑ i, (G.L c i - G.L b i) * ub i) ∧
        (∀ c : Fin k, c ∈ pmNeighbourhood G a b →
          (∑ i, (G.L c i - G.L a i) * ua i) +
          (∑ i, (G.L c i - G.L b i) * ub i) = Δ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c * (n : ℝ) ≤ pmMinimaxRegret G n := by
  sorry
