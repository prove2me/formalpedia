-- Prove2me | solution 1 for strict_supergraph_of_planar_edge_count_gap__p2m_d8aa4474_1bb0_4a8a_92a2_795d49f289c9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:58:47.320709+00:00
-- url     : https://prove2.me/submissions/1a1f1a08-466e-4f63-98bb-0fa001f91775

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K L : SimpleGraph V)
    (dK : DecidableRel K.Adj)
    (hKL : K ≤ L)
    (hsmall : (letI : DecidableRel K.Adj := dK
      K.edgeFinset.card < 3 * Fintype.card V - 6))
    (hcount : (letI : DecidableRel L.Adj := Classical.decRel L.Adj
      L.edgeFinset.card = 3 * Fintype.card V - 6)) :
    ¬ L ≤ K := by
  intro hLK
  have hEq : K = L := le_antisymm hKL hLK
  subst K
  have hdec : dK = Classical.decRel L.Adj := Subsingleton.elim _ _
  rw [hdec] at hsmall
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  change L.edgeFinset.card < 3 * Fintype.card V - 6 at hsmall
  change L.edgeFinset.card = 3 * Fintype.card V - 6 at hcount
  omega