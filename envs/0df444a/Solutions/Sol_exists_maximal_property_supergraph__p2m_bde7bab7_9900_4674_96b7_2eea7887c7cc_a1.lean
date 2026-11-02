-- Prove2me | solution 1 for exists_maximal_property_supergraph__p2m_bde7bab7_9900_4674_96b7_2eea7887c7cc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:38:05.432146+00:00
-- url     : https://prove2.me/submissions/ddc728fc-32ed-49f2-8970-a7a04ef7a4d3

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V)
    (hG : P G) :
    ∃ H : SimpleGraph V,
      (∀ u v : V, G.Adj u v → H.Adj u v) ∧
      P H ∧
      (∀ K : SimpleGraph V,
        (∀ u v : V, G.Adj u v → K.Adj u v) →
        P K →
        (∀ u v : V, H.Adj u v → K.Adj u v) →
        K = H) := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun H => G ≤ H ∧ P H)
  have hS : S.Nonempty := by
    refine ⟨G, ?_⟩
    simp [S, hG]
  obtain ⟨H, hHmem, hmax⟩ :=
    Finset.exists_max_image S (fun K : SimpleGraph V => K.edgeFinset.card) hS
  have hH : G ≤ H ∧ P H := (Finset.mem_filter.mp hHmem).2
  refine ⟨H, ?_, hH.2, ?_⟩
  · intro u v huv
    exact (SimpleGraph.le_iff_adj.mp hH.1) u v huv
  · intro K hGK hPK hHK
    have hK : K ∈ S := by
      apply Finset.mem_filter.mpr
      constructor
      · simp
      · exact ⟨SimpleGraph.le_iff_adj.mpr hGK, hPK⟩
    have hcard : K.edgeFinset.card ≤ H.edgeFinset.card := hmax K hK
    have hsubset : H.edgeFinset ⊆ K.edgeFinset :=
      SimpleGraph.edgeFinset_subset_edgeFinset.mpr hHK
    have hedge : H.edgeFinset = K.edgeFinset :=
      Finset.eq_of_subset_of_card_le hsubset hcard
    exact (SimpleGraph.edgeFinset_inj.mp hedge).symm