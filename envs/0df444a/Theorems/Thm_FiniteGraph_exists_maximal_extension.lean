-- Prove2me | Theorems.Thm_FiniteGraph_exists_maximal_extension
-- name    : FiniteGraph.exists_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:22:17.976879+00:00
-- url     : https://prove2.me/theorems/b6762e32-f9ff-4b25-b8e9-19e8e99b4fc4
-- title:
--   Maximal extension for a property on finite graphs
-- statement:
--   For any property of simple graphs on a finite linearly ordered vertex type, every graph satisfying that property has a supergraph satisfying it that is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem FiniteGraph.exists_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (H : SimpleGraph V) (hH : P H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ P K ∧
      ∀ J : SimpleGraph V, K ≤ J → P J → J = K := by sorry
