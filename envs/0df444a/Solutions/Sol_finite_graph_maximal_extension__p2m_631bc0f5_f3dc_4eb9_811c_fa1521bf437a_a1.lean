-- Prove2me | solution 1 for finite_graph_maximal_extension__p2m_631bc0f5_f3dc_4eb9_811c_fa1521bf437a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:57:45.190554+00:00
-- url     : https://prove2.me/submissions/466c0f94-ac5f-4af2-b39e-7d6fed47118e

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V)
    (hP : P H) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      P K ∧
      (∀ L : SimpleGraph V, P L →
        (∀ u v, K.Adj u v → L.Adj u v) → L = K) := by
  classical
  let s : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => H ≤ G ∧ P G
  have hs : s.Nonempty := by
    refine ⟨H, ?_⟩
    simp [s, hP]
  obtain ⟨K, hK, hmax⟩ :=
    Finset.exists_max_image s (fun G : SimpleGraph V => G.edgeSet.ncard) hs
  have hKprops : H ≤ K ∧ P K := by
    simpa [s] using hK
  have hHmem : H ∈ s := by
    simp [s, hP]
  refine ⟨K, ?_, ?_, hKprops.2, ?_⟩
  · exact SimpleGraph.le_iff_adj.mp hKprops.1
  · exact hmax H hHmem
  · intro L hPL hKL
    have hKLorder : K ≤ L := SimpleGraph.le_iff_adj.mpr hKL
    have hLmem : L ∈ s := by
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨le_trans hKprops.1 hKLorder, hPL⟩
    have hcount : L.edgeSet.ncard ≤ K.edgeSet.ncard := hmax L hLmem
    by_contra hne
    have hne' : K ≠ L := fun h => hne h.symm
    have hlt : K < L := lt_of_le_of_ne hKLorder hne'
    have hsubset : K.edgeSet ⊂ L.edgeSet :=
      SimpleGraph.edgeSet_ssubset_edgeSet.mpr hlt
    have hstrict : K.edgeSet.ncard < L.edgeSet.ncard :=
      Set.ncard_lt_ncard hsubset
    omega
