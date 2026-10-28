-- Prove2me | Theorems.Thm_FiniteGraph_edgeSet_ne_of_new_reachable
-- name    : FiniteGraph.edgeSet_ne_of_new_reachable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:23:40.00175+00:00
-- url     : https://prove2.me/theorems/34fb93f7-4c4e-4b1f-9701-ec51c5eb3d59
-- title:
--   A changed reachability relation forces different edge sets
-- statement:
--   If a pair of vertices is unreachable in one simple graph and reachable in another, their edge sets differ.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem FiniteGraph.edgeSet_ne_of_new_reachable
    {V : Type} [Fintype V]
    (F H : SimpleGraph V)
    (hnew : ∃ u v : V, ¬ F.Reachable u v ∧ H.Reachable u v) :
    H.edgeSet ≠ F.edgeSet := by sorry
