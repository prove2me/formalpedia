-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_unique_pareto_cover_best
-- name    : BanditAlgorithm.partial_monitoring_unique_pareto_cover_best
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T18:48:21.599641+00:00
-- url     : https://prove2.me/theorems/35b919aa-231e-4ca3-a3ac-fa303329e6b9
-- title:
--   Duplicate-free Pareto-cell cover captures every hindsight optimum
-- statement:
--   Every finite partial-monitoring game with at least one action and one outcome admits a nonempty finite set $S$ of Pareto-optimal actions with no two duplicate loss rows, such that every finite outcome sequence has a hindsight-optimal action in $S$. Equivalently, one may discard dominated and lower-dimensional cells and retain one representative of each duplicate full-dimensional cell without changing the set of attainable hindsight minima.
--
--   The proof uses the Baire category theorem for the finite closed cell cover of the compact simplex: full-dimensional cells have dense union, so every simplex point lies in a full-dimensional cell. A relative-interior argument identifies full-dimensionality with the formal affine-dimension predicate.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Cambridge University Press (2020), §37.2.1 and Lemma 37.7 setup, pp. 483–484. https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Analysis.Convex.Intrinsic

open scoped BigOperators
open Set Topology

theorem BanditAlgorithm.partial_monitoring_unique_pareto_cover_best
    {k d : ℕ} {𝕊 : Type*}
    (G : PartialMonitoringGame k d 𝕊) (hk : 0 < k) (hd : 0 < d) :
    ∃ S : Finset (Fin k), S.Nonempty ∧
      (∀ a ∈ S, ParetoOptimalAction G a) ∧
      (∀ a ∈ S, ∀ b ∈ S, (∀ i, G.L a i = G.L b i) → a = b) ∧
      (∀ (n : ℕ) (out : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (out t) ≤ ∑ t, G.L a (out t)) := by
  sorry
