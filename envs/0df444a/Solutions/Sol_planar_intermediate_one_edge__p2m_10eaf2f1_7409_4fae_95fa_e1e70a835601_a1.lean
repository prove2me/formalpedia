-- Prove2me | solution 1 for planar_intermediate_one_edge__p2m_10eaf2f1_7409_4fae_95fa_e1e70a835601_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:07:11.485453+00:00
-- url     : https://prove2.me/submissions/e49d7816-2de3-4485-9d06-e88c6ae4dd34

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G M : SimpleGraph V)
    (dG : DecidableRel G.Adj) (dM : DecidableRel M.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hGM : G ≤ M)
    (hlt : G.edgeFinset.card < M.edgeFinset.card) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      G ≤ K ∧
      K.edgeFinset.card = G.edgeFinset.card + 1 := by
  classical
  have hmiss : ∃ u v, M.Adj u v ∧ ¬ G.Adj u v := by
    by_contra h
    have hMG : M ≤ G := by
      intro u v huv
      by_contra hnot
      exact h ⟨u, v, huv, hnot⟩
    have hEq : G = M := le_antisymm hGM hMG
    subst M
    have hdec : dG = dM := Subsingleton.elim _ _
    cases hdec
    exact (not_lt_of_ge (show G.edgeFinset.card ≤ G.edgeFinset.card from le_rfl) hlt)
  obtain ⟨u, v, huv, hnot⟩ := hmiss
  let K : SimpleGraph V := G ⊔ SimpleGraph.edge u v
  letI : DecidableRel K.Adj := Classical.decRel _
  have hne : u ≠ v := M.ne_of_adj huv
  have hedge : SimpleGraph.edge u v ≤ M := by
    intro a b hab
    rw [SimpleGraph.edge_adj] at hab
    rcases hab with ⟨hab, _⟩
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact huv
    · exact huv.symm
  have hKM : K ≤ M := sup_le hGM hedge
  have hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K := by
    rcases hM with ⟨p, arc, hp, hdraw, hcross⟩
    refine ⟨p, arc, hp, ?_, ?_⟩
    · intro a b hab hKad
      exact hdraw a b hab (hKM hKad)
    · intro a b c d hab hcd hKab hKcd hne' t ht s hs hEq'
      exact hcross a b c d hab hcd (hKM hKab) (hKM hKcd) hne' t ht s hs hEq'
  refine ⟨K, inferInstance, hKplanar, ?_, ?_⟩
  · exact le_sup_left
  · simpa [K] using G.card_edgeFinset_sup_edge hnot hne