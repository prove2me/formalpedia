-- Prove2me | Theorems.Thm_FiniteGraph_connected_supergraph_of_step
-- name    : FiniteGraph.connected_supergraph_of_step
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T12:55:26.216499+00:00
-- url     : https://prove2.me/theorems/36dc7ff2-2ed9-40b2-8660-628750ffa57c
-- title:
--   Iterate reachability-merging graph extensions
-- statement:
--   For a finite vertex type, if every disconnected supergraph satisfying a property admits a property-preserving supergraph extension that connects some formerly unreachable pair, then there is a connected supergraph satisfying the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem FiniteGraph.connected_supergraph_of_step
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V)
    (hG : P G)
    (hstep : ∀ F : SimpleGraph V, G.edgeSet ⊆ F.edgeSet → P F → ¬ F.Connected →
      ∃ H : SimpleGraph V,
        F.edgeSet ⊆ H.edgeSet ∧ P H ∧
          ∃ u v : V, ¬ F.Reachable u v ∧ H.Reachable u v) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧ P H ∧ H.Connected := by sorry
