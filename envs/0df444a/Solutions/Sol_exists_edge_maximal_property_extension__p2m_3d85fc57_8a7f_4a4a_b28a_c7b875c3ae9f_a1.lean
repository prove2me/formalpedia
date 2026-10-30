-- Prove2me | solution 1 for exists_edge_maximal_property_extension__p2m_3d85fc57_8a7f_4a4a_b28a_c7b875c3ae9f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:02:54.246151+00:00
-- url     : https://prove2.me/submissions/85ebae4e-4775-46e2-834a-2194cd15ba6e

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (H : SimpleGraph V)
    (hP : P H) :
    ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ P K ∧
      ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet → ¬ P L := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => H.edgeSet ⊆ G.edgeSet ∧ P G
  have hHmem : H ∈ candidates := by
    simp [candidates, hP]
  obtain ⟨K, hKmem, hKmax⟩ :=
    Finset.exists_max_image candidates (fun G => G.edgeSet.ncard) ⟨H, hHmem⟩
  have hKprops : H.edgeSet ⊆ K.edgeSet ∧ P K := by
    simpa only [candidates, Finset.mem_filter, Finset.mem_univ, true_and] using hKmem
  refine ⟨K, hKprops.1, hKprops.2, ?_⟩
  intro L hKL hPL
  have hLmem : L ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hKprops.1.trans hKL.subset, hPL⟩
  have hcard : K.edgeSet.ncard < L.edgeSet.ncard :=
    Set.ncard_lt_ncard hKL
  exact (not_le_of_gt hcard) (hKmax L hLmem)