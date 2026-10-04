-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_divergence_cut
-- name    : EdmondsKarp.ShortestPath.divergence_cut
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T19:35:27.462122+00:00
-- url     : https://prove2.me/theorems/542b6027-7e95-4aa9-bc07-fe25dde672cc
-- title:
--   Summed divergence equals outward cut flow
-- statement:
--   For any real function on ordered vertex pairs and any set S of vertices, summing outgoing-minus-incoming differences over S equals the same sum restricted to pairs with the first vertex in S and the second outside S.
-- source:
--   Auxiliary lemmas for the augmenting-path optimality criterion in Edmonds and Karp (1972), §1.1 p. 249. DOI: 10.1145/321694.321699.

import Mathlib

theorem EdmondsKarp.ShortestPath.divergence_cut {V : Type} [Fintype V] [DecidableEq V] (d : V → V → ℝ) (S : Finset V) :
    (∑ u ∈ S, ∑ v : V, (d u v - d v u)) =
      ∑ u ∈ S, ∑ v ∈ Sᶜ, (d u v - d v u) := by sorry
