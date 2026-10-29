-- Prove2me | solution 1 for finite_graph_maximal_extension__p2m_eee70f1a_2d3d_4378_a78c_629ec2b9156c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:47:02.281015+00:00
-- url     : https://prove2.me/submissions/f5af90ca-15bf-4875-bffd-006cd562e684

import Mathlib

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hP : ∀ G F : SimpleGraph V,
      G.edgeSet ⊆ F.edgeSet → P F → P G)
    (H : SimpleGraph V)
    (hH : P H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      P K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        P L →
        L.edgeSet ⊆ K.edgeSet := by
  classical
  let admissible : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => H.edgeSet ⊆ G.edgeSet ∧ P G
  have admissible_nonempty : admissible.Nonempty := by
    refine ⟨H, ?_⟩
    simp [admissible, hH]
  obtain ⟨K, hKmem, hKmax⟩ :=
    Finset.exists_max_image admissible (fun G => G.edgeFinset.card) admissible_nonempty
  have hKprop : H.edgeSet ⊆ K.edgeSet ∧ P K := by
    simpa [admissible] using hKmem
  refine ⟨K, hKprop.1, hKprop.2, ?_⟩
  intro L hKL hPL
  have hLmem : L ∈ admissible := by
    simp only [admissible, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hKprop.1.trans hKL, hPL⟩
  have hcard : L.edgeFinset.card ≤ K.edgeFinset.card := hKmax L hLmem
  have hsubset : K.edgeFinset ⊆ L.edgeFinset := by
    simpa using hKL
  have heq : K.edgeFinset = L.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsubset hcard
  have hgraph : K = L := SimpleGraph.edgeFinset_inj.mp heq
  rw [hgraph]