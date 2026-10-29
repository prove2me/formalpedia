-- Prove2me | solution 1 for finite_property_maximal_graph_extension__p2m_af5ef936_754d_4f1b_a8c0_025d8e67bd44_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:03:27.494212+00:00
-- url     : https://prove2.me/submissions/20613f31-ca8d-4b59-82db-b0a36104bf0d

import Mathlib

set_option autoImplicit false

theorem _root_.solution
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
  haveI : Finite (SimpleGraph V) :=
    Finite.of_injective (fun G : SimpleGraph V => G.Adj) (fun _ _ h => SimpleGraph.ext h)
  obtain ⟨H, hH⟩ := (Set.toFinite {H : SimpleGraph V | G ≤ H ∧ P H}).exists_maximal ⟨G, le_rfl, hG⟩
  refine ⟨H, SimpleGraph.edgeSet_subset_edgeSet.2 hH.1.1, hH.1.2, fun K hK hPK => ?_⟩
  have hHK : H ≤ K := SimpleGraph.edgeSet_subset_edgeSet.1 hK
  rw [le_antisymm hHK (hH.2 ⟨hH.1.1.trans hHK, hPK⟩ hHK)]
