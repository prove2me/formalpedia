-- Prove2me | Theorems.Thm_FiniteSimpleGraph_exists_maximal_supergraph__p2m_ebc26ecc_dfea_4863_8cab_260c69e4997d_a2
-- name    : FiniteSimpleGraph.exists_maximal_supergraph__p2m_ebc26ecc_dfea_4863_8cab_260c69e4997d_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:26:12.684604+00:00
-- url     : https://prove2.me/theorems/c72d6c70-303f-4dda-aab8-90cecf43027e
-- title:
--   A finite graph predicate has a maximal supergraph
-- statement:
--   On a finite vertex type, any graph satisfying a predicate has a supergraph satisfying that predicate which is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Basic

theorem FiniteSimpleGraph.exists_maximal_supergraph__p2m_ebc26ecc_dfea_4863_8cab_260c69e4997d_a2
    {V : Type} [Fintype V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hG : P G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ P K ∧
      (∀ H : SimpleGraph V,
        G ≤ H → P H → K ≤ H → H ≤ K) := by sorry
