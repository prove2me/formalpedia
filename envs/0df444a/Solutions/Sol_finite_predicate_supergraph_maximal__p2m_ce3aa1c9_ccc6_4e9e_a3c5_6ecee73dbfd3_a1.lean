-- Prove2me | solution 1 for finite_predicate_supergraph_maximal__p2m_ce3aa1c9_ccc6_4e9e_a3c5_6ecee73dbfd3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:58:21.020944+00:00
-- url     : https://prove2.me/submissions/1bd9fa35-4922-4481-a83a-e423c0ca7fe4

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (G : SimpleGraph V)
    (hG : P G) : ∃ K : SimpleGraph V, G ≤ K ∧ P K ∧
      (∀ L : SimpleGraph V, K ≤ L → P L → L = K) := by
  classical
  let feasible : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun H => G ≤ H ∧ P H)
  have hfeasible : feasible.Nonempty := by
    refine ⟨G, ?_⟩
    simp [feasible, hG]
  obtain ⟨K, hKmem, hKmax⟩ :=
    Finset.exists_max_image feasible (fun H => Fintype.card H.edgeSet) hfeasible
  have hK : G ≤ K ∧ P K := (Finset.mem_filter.mp hKmem).2
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hPL
  have hLmem : L ∈ feasible := by
    simp only [feasible, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hK.1.trans hKL, hPL⟩
  by_contra hne
  have hne' : K ≠ L := fun heq => hne heq.symm
  have hlt : K < L := lt_of_le_of_ne hKL hne'
  have hcard : Fintype.card K.edgeSet < Fintype.card L.edgeSet :=
    Set.card_lt_card (SimpleGraph.edgeSet_ssubset_edgeSet.mpr hlt)
  exact (not_le_of_gt hcard) (hKmax L hLmem)