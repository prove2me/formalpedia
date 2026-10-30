-- Prove2me | solution 1 for finite_maximal_simpleGraph_extension__p2m_5ee8e196_64c4_419c_bd20_94ce32b8d5fd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:49:32.643715+00:00
-- url     : https://prove2.me/submissions/e066a0f9-d83d-4370-87bd-a98105cf2085

import Mathlib

theorem solution {V : Type} [Fintype V] (P : SimpleGraph V → Prop)
    (K : SimpleGraph V) (hK : P K) :
    ∃ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet ∧ P L ∧
      ∀ M : SimpleGraph V, L.edgeSet ⊆ M.edgeSet → P M → M.edgeSet = L.edgeSet := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G => K ≤ G ∧ P G)
  have hS : S.Nonempty := by
    refine ⟨K, ?_⟩
    simp [S, hK]
  obtain ⟨L, hL, hmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeFinset.card) hS
  refine ⟨L, ?_, ?_, ?_⟩
  · exact SimpleGraph.edgeSet_subset_edgeSet.mpr (Finset.mem_filter.mp hL).2.1
  · exact (Finset.mem_filter.mp hL).2.2
  · intro M hLM hPM
    have hLM' : L ≤ M := SimpleGraph.edgeSet_subset_edgeSet.mp hLM
    have hKL : K ≤ L := (Finset.mem_filter.mp hL).2.1
    have hKM : K ≤ M := le_trans hKL hLM'
    have hM : M ∈ S := by
      simp [S, hKM, hPM]
    have hcard : M.edgeFinset.card ≤ L.edgeFinset.card := hmax M hM
    have hsub : L.edgeFinset ⊆ M.edgeFinset :=
      SimpleGraph.edgeFinset_subset_edgeFinset.mpr hLM'
    have heq : L.edgeFinset = M.edgeFinset :=
      Finset.eq_of_subset_of_card_le hsub hcard
    have hgraph : M = L := (SimpleGraph.edgeFinset_inj.mp heq).symm
    simpa [hgraph]