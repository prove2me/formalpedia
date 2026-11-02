-- Prove2me | solution 1 for finite_maximal_planar_property_extension__p2m_503a8d71_6799_480d_8f3e_33232e674c95_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:45:06.473102+00:00
-- url     : https://prove2.me/submissions/59e37d2d-8351-41cc-9b24-1bc020f807c3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : P M) :
    ∃ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      P N ∧
      (letI : DecidableRel M.Adj := dM
       letI : DecidableRel N.Adj := dN
       M.edgeFinset ⊆ N.edgeFinset) ∧
      (∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
        P K →
        (letI : DecidableRel N.Adj := dN
         letI : DecidableRel K.Adj := dK
         N.edgeFinset ⊆ K.edgeFinset) →
        N = K) := by
  classical
  let Q : SimpleGraph V → Prop := fun G => P G ∧ M ≤ G
  obtain ⟨N, dN, hExt⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists Q).2 ⟨M, hM, le_rfl⟩
  refine ⟨N, dN, hExt.1.1, ?_, ?_⟩
  · exact (SimpleGraph.edgeFinset_subset_edgeFinset).2 hExt.1.2
  · intro K dK
    letI : DecidableRel N.Adj := dN
    letI : DecidableRel K.Adj := dK
    intro hK hSub
    have hNK : N ≤ K := (SimpleGraph.edgeFinset_subset_edgeFinset).1 hSub
    have hMK : M ≤ K := le_trans hExt.1.2 hNK
    have hQK : Q K := ⟨hK, hMK⟩
    exact (hExt.le_iff_eq hQK).mp hNK