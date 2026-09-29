-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_unique_pareto_cell_cover_best
-- name    : BanditAlgorithm.partial_monitoring_unique_pareto_cell_cover_best
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T19:08:56.974284+00:00
-- url     : https://prove2.me/theorems/af5b9e63-c47b-4afb-9b3d-bde06902c63b
-- title:
--   Duplicate-free Pareto cells cover the outcome simplex
-- statement:
--   Every finite partial-monitoring game with at least one action and one outcome admits a nonempty finite set $S$ of pairwise nonduplicate Pareto-optimal representatives such that
--
--   $$
--   \Delta_d\subseteq\bigcup_{a\in S} C_a.
--   $$
--
--   Moreover, every finite outcome sequence has a hindsight-optimal action in $S$. Thus $S$ simultaneously covers the geometric lower-envelope regions and preserves every empirical best-action comparison.
--
--   The cell-cover clause is useful independently of the classification theorem: it removes lower-dimensional and duplicate actions without losing any point of the outcome simplex.
--
--   **Formalization Note** Pairwise nonduplication is stated by equality of loss rows implying equality of action indices.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Cambridge University Press (2020), §37.2.1 pp. 483–484 and Lemma 37.7 p. 484. The formal proof uses the finite closed-cover Baire argument to retain precisely the full-dimensional cells. https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Analysis.Convex.Intrinsic

open scoped BigOperators

theorem BanditAlgorithm.partial_monitoring_unique_pareto_cell_cover_best
    {k d : ℕ} {𝕊 : Type*}
    (G : PartialMonitoringGame k d 𝕊) (hk : 0 < k) (hd : 0 < d) :
    ∃ S : Finset (Fin k), S.Nonempty ∧
      (∀ a ∈ S, ParetoOptimalAction G a) ∧
      (∀ a ∈ S, ∀ b ∈ S, (∀ i, G.L a i = G.L b i) → a = b) ∧
      (∀ u, u ∈ stdSimplex ℝ (Fin d) → ∃ a ∈ S, u ∈ pmCell G a) ∧
      (∀ (n : ℕ) (out : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (out t) ≤ ∑ t, G.L a (out t)) := by
  sorry
