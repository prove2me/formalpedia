-- Prove2me | solution 2 for finite_property_maximal_graph_extension__p2m_af5ef936_754d_4f1b_a8c0_025d8e67bd44_a1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:12:53.121687+00:00
-- url     : https://prove2.me/submissions/5bb33c64-26c4-46cc-92b8-710bac3ba198

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V)
    (hG : P G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      P H ∧
      ∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet →
        P K →
        H.edgeSet = K.edgeSet := by
  obtain ⟨H, hGH, hmax⟩ := Finite.exists_le_maximal (p := P) hG
  refine ⟨H, SimpleGraph.edgeSet_subset_edgeSet.mpr hGH, hmax.prop, ?_⟩
  intro K hHK hK
  have h1 : H ≤ K := SimpleGraph.edgeSet_subset_edgeSet.mp hHK
  have h2 : K ≤ H := hmax.2 hK h1
  rw [le_antisymm h1 h2]
