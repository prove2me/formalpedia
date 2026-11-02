-- Prove2me | solution 1 for finite_graph_maximal_extension__p2m_0d55c294_ea6d_4f9f_a448_4b66814798e5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:21:42.244206+00:00
-- url     : https://prove2.me/submissions/28939b0e-125b-4e72-89e7-d71a193997ef

import Mathlib

open Finset

theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P G) :
    letI : ∀ H : SimpleGraph V, DecidableRel H.Adj :=
      fun H => Classical.decRel H.Adj
    ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
      (∀ J : SimpleGraph V, P J → H ≤ J → J = H) ∧
      G.edgeFinset.card ≤ H.edgeFinset.card := by
  classical
  let Q : SimpleGraph V → Prop := fun H => P H ∧ G ≤ H
  obtain ⟨H, x, hH⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (V := V) Q).2
      ⟨G, hP, le_rfl⟩
  have hx : x = Classical.decRel H.Adj := Subsingleton.elim _ _
  subst x
  refine ⟨H, hH.1.2, hH.1.1, ?_, ?_⟩
  · intro J hPJ hHJ
    have hQJ : Q J := ⟨hPJ, le_trans hH.1.2 hHJ⟩
    symm
    exact (SimpleGraph.IsExtremal.le_iff_eq hH hQJ).mp hHJ
  · exact Finset.card_le_card
      ((SimpleGraph.edgeFinset_subset_edgeFinset (G₁ := G) (G₂ := H)).2 hH.1.2)