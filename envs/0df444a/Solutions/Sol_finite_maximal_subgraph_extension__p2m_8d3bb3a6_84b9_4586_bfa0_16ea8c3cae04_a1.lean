-- Prove2me | solution 1 for finite_maximal_subgraph_extension__p2m_8d3bb3a6_84b9_4586_bfa0_16ea8c3cae04_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:54:35.045808+00:00
-- url     : https://prove2.me/submissions/fa408b33-5b64-4fdd-bc53-9a90165a97a1

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000 in

theorem solution
    {V : Type} [Fintype V]
    (U : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hU : P U)
    (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G) :
    ∃ W : SimpleGraph V, U ≤ W ∧ P W ∧
      ∀ N : SimpleGraph V, W ≤ N → P N → N ≤ W := by
  classical
  let S : Set (SimpleGraph V) := {G | U ≤ G ∧ P G}
  let f : SimpleGraph V → Finset (Sym2 V) := fun G => G.edgeSet.toFinset
  have hS : S.Nonempty := ⟨U, by simp [S, hU]⟩
  have hfin : (f '' S).Finite :=
    Set.finite_univ.subset (by
      intro x hx
      exact Set.mem_univ x)
  obtain ⟨W, hWS, hmax⟩ := hfin.exists_maximalFor' f S hS
  change U ≤ W ∧ P W at hWS
  refine ⟨W, hWS.1, hWS.2, ?_⟩
  intro N hWN hPN
  have hNS : N ∈ S := by
    change U ≤ N ∧ P N
    exact ⟨le_trans hWS.1 hWN, hPN⟩
  have hsub : W.edgeSet ⊆ N.edgeSet :=
    SimpleGraph.edgeSet_subset_edgeSet.mpr hWN
  have hfsub : f W ⊆ f N := by
    change W.edgeSet.toFinset ⊆ N.edgeSet.toFinset
    exact Set.toFinset_subset_toFinset.mpr hsub
  have hfrev : f N ⊆ f W := hmax hNS hfsub
  have hrev : N.edgeSet ⊆ W.edgeSet := by
    change N.edgeSet.toFinset ⊆ W.edgeSet.toFinset at hfrev
    exact Set.toFinset_subset_toFinset.mp hfrev
  exact SimpleGraph.edgeSet_subset_edgeSet.mp hrev