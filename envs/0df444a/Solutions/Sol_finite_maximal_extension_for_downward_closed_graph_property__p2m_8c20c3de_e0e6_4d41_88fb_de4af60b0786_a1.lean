-- Prove2me | solution 1 for finite_maximal_extension_for_downward_closed_graph_property__p2m_8c20c3de_e0e6_4d41_88fb_de4af60b0786_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:51:14.354909+00:00
-- url     : https://prove2.me/submissions/eddb4ab5-c2fc-4253-9ddf-a3abeee628d7

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] (P : SimpleGraph V → Prop)
    (hdown : ∀ {G K : SimpleGraph V}, G ≤ K → P K → P G)
    (H : SimpleGraph V) (hH : P H) :
    ∃ T : SimpleGraph V, H ≤ T ∧ P T ∧
      ∀ T' : SimpleGraph V, T ≤ T' → P T' → T' = T := by
  classical
  let admissible : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => H ≤ G ∧ P G
  have hAdmissible : admissible.Nonempty := by
    refine ⟨H, ?_⟩
    simp [admissible, hH]
  obtain ⟨T, hTmem, hTmax⟩ :=
    Finset.exists_max_image admissible (fun G : SimpleGraph V => G.edgeFinset.card)
      hAdmissible
  have hHT : H ≤ T := by
    simpa [admissible] using (Finset.mem_filter.mp hTmem).2.1
  have hPT : P T := by
    simpa [admissible] using (Finset.mem_filter.mp hTmem).2.2
  refine ⟨T, hHT, hPT, ?_⟩
  intro T' hTT' hPT'
  have hT'mem : T' ∈ admissible := by
    simp [admissible, le_trans hHT hTT', hPT']
  have hcard : T'.edgeFinset.card ≤ T.edgeFinset.card := hTmax T' hT'mem
  by_contra hne
  have hstrict : T < T' := lt_of_le_of_ne hTT' (Ne.symm hne)
  have hstrictEdges : T.edgeFinset ⊂ T'.edgeFinset :=
    (SimpleGraph.edgeFinset_ssubset_edgeFinset).2 hstrict
  have hcardlt : T.edgeFinset.card < T'.edgeFinset.card := Finset.card_lt_card hstrictEdges
  omega
