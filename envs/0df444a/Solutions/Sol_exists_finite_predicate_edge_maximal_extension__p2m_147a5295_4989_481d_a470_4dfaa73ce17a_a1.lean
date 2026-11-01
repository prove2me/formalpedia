-- Prove2me | solution 1 for exists_finite_predicate_edge_maximal_extension__p2m_147a5295_4989_481d_a470_4dfaa73ce17a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:11:56.584552+00:00
-- url     : https://prove2.me/submissions/34622979-6bc4-47ba-86b2-fcbc3e402a66

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (N : SimpleGraph V)
    (dN : DecidableRel N.Adj) (hN : P N) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      P K ∧
      N.edgeFinset ⊆ K.edgeFinset ∧
      ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
        P L →
        K.edgeFinset ⊆ L.edgeFinset →
        L.edgeFinset ⊆ K.edgeFinset := by
  classical
  let S : Set (SimpleGraph V) := {G | P G ∧ N ≤ G}
  have hSfin : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨N, by simp [S, hN]⟩
  obtain ⟨K, hK, hKmax⟩ := hSfin.exists_maximal hSne
  let dK : DecidableRel K.Adj := Classical.decRel _
  refine ⟨K, dK, hK.1, ?_, ?_⟩
  · exact SimpleGraph.edgeFinset_subset_edgeFinset.mpr hK.2
  · intro L dL hL hKL
    have hKL' : K ≤ L := SimpleGraph.edgeFinset_subset_edgeFinset.mp hKL
    have hNL : N ≤ L := hK.2.trans hKL'
    have hLmem : L ∈ S := ⟨hL, hNL⟩
    have hLK : L ≤ K := hKmax hLmem hKL'
    exact SimpleGraph.edgeFinset_subset_edgeFinset.mpr hLK